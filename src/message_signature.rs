use std::collections::HashSet;

use anyhow::{Context, Result, anyhow, bail};
use base64::{Engine as _, engine::general_purpose::STANDARD};
use httpsig_hyper::prelude::{
    AlgorithmName, HttpSigResult, HttpSignatureParams, SecretKey, SharedKey, SigningKey,
    message_component::{HttpMessageComponentId, HttpMessageComponentName},
};
use hyper::http;
use reqwest::blocking::{Body as ReqwestBody, Request};
use reqwest::header::{HeaderName, HeaderValue};
use sha2::{Digest, Sha256};

pub fn sign_request(
    request: &mut Request,
    key_id: &str,
    key_material: &str,
    components: Option<&[String]>,
    algorithm_override: Option<AlgorithmName>,
) -> Result<()> {
    let key = parse_key_input(key_material)?;

    let (signing_key, algorithm) = build_signing_key(&key, key_id, algorithm_override)?;

    let components = resolve_components(request, components);
    ensure_content_digest(request, &components)?;

    let mut signature_params = build_signature_params(&components)?;
    signature_params.set_alg(&algorithm);

    // Ensure keyid is included in Signature-Input
    signature_params.set_keyid(key_id);

    // Preferred path: use upstream sync signing helper.
    let mut http_request = http::Request::builder()
        .version(request.version())
        .method(request.method())
        .uri(request.url().as_str())
        .body(reqwest::Body::default())
        .context("message-signature: Failed to build temporary HTTP request")?;
    *http_request.headers_mut() = request.headers().clone();

    use httpsig_hyper::MessageSignatureReqSync;
    http_request
        .set_message_signature_sync(&signature_params, &signing_key, Some("sig1"))
        .context("message-signature: Failed to set message signature")?;

    let signature = http_request
        .headers()
        .get("signature")
        .context("message-signature: Signature header missing after signing")?;
    let signature_input = http_request
        .headers()
        .get("signature-input")
        .context("message-signature: Signature-Input header missing after signing")?;

    request
        .headers_mut()
        .insert(HeaderName::from_static("signature"), signature.clone());
    request.headers_mut().insert(
        HeaderName::from_static("signature-input"),
        signature_input.clone(),
    );
    Ok(())
}

/// Resolves and expands message components for signature coverage.
///
/// This function handles:
/// - Default components: If no components are specified, uses @method, @authority, @target-uri
/// - @query-params expansion: Expands into individual @query-param components for each parameter
/// - content-digest: Only includes if the request has a body
///
/// Note: @query-params is not a standard RFC 9421 component, but is commonly used as a
/// convenience shorthand to sign all query parameters without listing them individually.
fn resolve_components(request: &Request, components: Option<&[String]>) -> Vec<String> {
    let mut resolved = Vec::new();
    let source = if let Some(c) = components {
        c
    } else {
        // RFC 9421 recommended minimal set for request signing
        &[
            "@method".to_string(),
            "@authority".to_string(),
            "@target-uri".to_string(),
        ] as &[String]
    };

    for component in source {
        if component == "@query-params" {
            // According to some conventions (and this implementation), "@query-params"
            // acts as a wildcard that expands into individual "@query-param" components
            // for every parameter present in the request's query string.
            //
            // RFC 9421 does not define "@query-params" as a standard derived component,
            // but many implementations use it to simplify signing all query parameters
            // without listing them explicitly.
            if let Some(query) = request.url().query() {
                let mut seen = HashSet::new();
                for (name, _) in form_urlencoded::parse(query.as_bytes()) {
                    if seen.insert(name.to_string()) {
                        resolved.push(format!("@query-param;name=\"{}\"", name));
                    }
                }
            }
        } else if component == "content-digest" {
            if request.body().is_some() {
                resolved.push(component.clone());
            }
        } else {
            resolved.push(component.clone());
        }
    }
    resolved
}

/// Ensures the Content-Digest header is present if it's a covered component.
///
/// According to RFC 9530, the Content-Digest header uses the format:
/// `sha-256=:<base64-encoded-hash>:`
///
/// This function:
/// 1. Checks if "content-digest" is in the covered components
/// 2. If yes and the header is missing, computes SHA-256 of the request body
/// 3. Adds the Content-Digest header in the RFC 9530 format
fn ensure_content_digest(request: &mut Request, components: &[String]) -> Result<()> {
    if components
        .iter()
        .any(|c| c.eq_ignore_ascii_case("content-digest"))
        && !request.headers().contains_key("content-digest")
        && request.body().is_some()
    {
        let bytes = buffer_request_body(request)?;
        let digest = Sha256::digest(&bytes);
        // RFC 9530 format: algorithm=:base64-hash:
        let value = format!("sha-256=:{}:", STANDARD.encode(digest));
        request.headers_mut().insert(
            HeaderName::from_static("content-digest"),
            HeaderValue::from_str(&value)?,
        );
    }
    Ok(())
}

fn build_signature_params(components: &[String]) -> Result<HttpSignatureParams> {
    let mut component_ids = Vec::new();
    let mut seen = HashSet::new();
    for c in components {
        let normalized = normalize_component_id(c);
        let id = HttpMessageComponentId::try_from(normalized.as_str())
            .with_context(|| format!("message-signature: Invalid component: {}", c))?;
        // RFC 9421 requires each covered component identifier to appear at most once.
        // Equivalence is based on component id semantics, where parameter order does
        // not create a distinct identifier.
        let uniqueness_key = component_uniqueness_key(&id);
        if !seen.insert(uniqueness_key) {
            bail!(
                "message-signature: Duplicate covered component identifier: {}",
                id
            );
        }
        component_ids.push(id);
    }
    HttpSignatureParams::try_new(&component_ids)
        .context("message-signature: Failed to create signature params")
}

/// Build a canonical key for RFC 9421 component-identifier uniqueness checks.
///
/// RFC 9421 treats component identifiers as unique entries in covered components,
/// and two identifiers that differ only by parameter ordering are equivalent.
/// We normalize:
/// - component name (`HttpField` lowercased, derived names preserved), and
/// - parameters (sorted, then joined),
///
/// so equivalent identifiers map to the same key.
fn component_uniqueness_key(component_id: &HttpMessageComponentId) -> String {
    let name = match &component_id.name {
        HttpMessageComponentName::Derived(derived) => AsRef::<str>::as_ref(derived).to_string(),
        HttpMessageComponentName::HttpField(field) => field.to_ascii_lowercase(),
    };
    let mut params: Vec<String> = component_id
        .params
        .0
        .iter()
        .cloned()
        .map(Into::into)
        .collect();
    params.sort_unstable();
    if params.is_empty() {
        name
    } else {
        format!("{name};{}", params.join(";"))
    }
}

/// Normalizes component identifiers for RFC 9421 compliance.
///
/// According to RFC 9421, derived components (starting with @) that have parameters
/// must be quoted. For example:
/// - `@query-param;name="foo"` -> `"@query-param";name="foo"`
/// - `@method` -> `@method` (no parameters, no quotes needed)
/// - `content-type` -> `content-type` (not a derived component)
///
/// This normalization is required for proper signature base construction.
fn normalize_component_id(component: &str) -> String {
    if let Some(idx) = component.find(';') {
        let (name, params) = component.split_at(idx);
        if name.starts_with('@') && !name.starts_with('"') {
            // Derived component with parameters must be quoted
            return format!("\"{}\"{}", name, params);
        }
    }
    component.to_string()
}

fn buffer_request_body(request: &mut Request) -> Result<Vec<u8>> {
    if let Some(body) = request.body_mut() {
        let bytes = body
            .buffer()
            .context("message-signature: Failed to buffer request body for Content-Digest")?
            .to_vec();
        *body = ReqwestBody::from(bytes.clone());
        Ok(bytes)
    } else {
        Ok(Vec::new())
    }
}

fn parse_key_input(key_material: &str) -> Result<Vec<u8>> {
    let key = if let Some(path) = key_material.strip_prefix('@') {
        std::fs::read(crate::utils::expand_tilde(path))?
    } else {
        // Unlike some HTTPie plugins that force Base64 encoding for the secret key part
        // of the --auth string, xh treats the raw string as the key material by default.
        // This provides a more direct CLI experience, consistent with how xh handles
        // standard passwords in `-a user:password`.
        key_material.as_bytes().to_vec()
    };
    Ok(key)
}

fn build_signing_key(
    key_material: &[u8],
    key_id: &str,
    algorithm_override: Option<AlgorithmName>,
) -> Result<(MessageSigningKey, AlgorithmName)> {
    if let Some(algorithm) = algorithm_override {
        return build_signing_key_with_algorithm(key_material, key_id, &algorithm);
    }

    if let Ok(pem) = std::str::from_utf8(key_material) {
        if pem.contains("-----BEGIN") {
            if let Some(secret) = parse_pem_secret_key(
                pem,
                &[
                    AlgorithmName::Ed25519,
                    AlgorithmName::EcdsaP256Sha256,
                    AlgorithmName::EcdsaP384Sha384,
                ],
            ) {
                let alg = secret.alg();
                return Ok((MessageSigningKey::Secret(secret, key_id.to_string()), alg));
            }
            if parse_pem_secret_key(
                pem,
                &[AlgorithmName::RsaV1_5Sha256, AlgorithmName::RsaPssSha512],
            )
            .is_some()
            {
                bail!(
                    "message-signature: RSA private keys require an explicit algorithm. Use --unstable-m-sig-alg=rsa-v1_5-sha256 or --unstable-m-sig-alg=rsa-pss-sha512"
                );
            }
            bail!(
                "message-signature: Failed to parse PEM private key. Supported algorithms: ed25519, ecdsa-p256-sha256, ecdsa-p384-sha384, rsa-v1_5-sha256, rsa-pss-sha512"
            );
        }
    }

    build_hmac_signing_key(key_material, key_id)
}

fn build_hmac_signing_key(
    key_material: &[u8],
    key_id: &str,
) -> Result<(MessageSigningKey, AlgorithmName)> {
    let encoded = STANDARD.encode(key_material);
    let shared_key = SharedKey::from_base64(&AlgorithmName::HmacSha256, &encoded)
        .map_err(|e| anyhow!("message-signature: Failed to create HMAC key: {:?}", e))?;
    Ok((
        MessageSigningKey::Shared(shared_key, key_id.to_string()),
        AlgorithmName::HmacSha256,
    ))
}

fn build_signing_key_with_algorithm(
    key_material: &[u8],
    key_id: &str,
    algorithm: &AlgorithmName,
) -> Result<(MessageSigningKey, AlgorithmName)> {
    if algorithm == &AlgorithmName::HmacSha256 {
        return build_hmac_signing_key(key_material, key_id);
    }

    let secret = if let Ok(pem) = std::str::from_utf8(key_material) {
        if pem.contains("-----BEGIN") {
            SecretKey::from_pem(algorithm, pem).with_context(|| {
                format!(
                    "message-signature: Failed to parse PEM private key as {}",
                    algorithm.as_str()
                )
            })?
        } else {
            SecretKey::from_bytes(algorithm, key_material).with_context(|| {
                format!(
                    "message-signature: Failed to parse private key bytes as {}",
                    algorithm.as_str()
                )
            })?
        }
    } else {
        SecretKey::from_bytes(algorithm, key_material).with_context(|| {
            format!(
                "message-signature: Failed to parse private key bytes as {}",
                algorithm.as_str()
            )
        })?
    };
    let alg = secret.alg();
    Ok((MessageSigningKey::Secret(secret, key_id.to_string()), alg))
}

fn parse_pem_secret_key(pem: &str, algorithms: &[AlgorithmName]) -> Option<SecretKey> {
    for alg in algorithms {
        if let Ok(secret) = SecretKey::from_pem(alg, pem) {
            return Some(secret);
        }
    }
    None
}

enum MessageSigningKey {
    Secret(SecretKey, String),
    Shared(SharedKey, String),
}

impl SigningKey for MessageSigningKey {
    fn sign(&self, data: &[u8]) -> HttpSigResult<Vec<u8>> {
        match self {
            MessageSigningKey::Secret(inner, _) => inner.sign(data),
            MessageSigningKey::Shared(inner, _) => inner.sign(data),
        }
    }

    fn key_id(&self) -> String {
        match self {
            MessageSigningKey::Secret(_, id) => id.clone(),
            MessageSigningKey::Shared(_, id) => id.clone(),
        }
    }

    fn alg(&self) -> AlgorithmName {
        match self {
            MessageSigningKey::Secret(inner, _) => inner.alg(),
            MessageSigningKey::Shared(inner, _) => inner.alg(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use reqwest::blocking::Client;

    #[test]
    fn test_content_digest_generation() {
        let mut req = Client::new()
            .post("http://example.com")
            .body("Hello, World!")
            .build()
            .unwrap();

        let components = vec!["content-digest".to_string()];
        ensure_content_digest(&mut req, &components).unwrap();

        let digest_header = req.headers().get("content-digest").unwrap();
        let digest_str = digest_header.to_str().unwrap();

        // SHA-256 of "Hello, World!" is dffd6021bb2bd5b0af676290809ec3a53191dd81c7f70a4b28688a362182986f
        // Base64: 3/1gIbsr1bCvZ2KQgJ7DpTGR3YHH9wpLKGiKNiGCmG8=
        // Header format: sha-256=:...:
        assert_eq!(
            digest_str,
            "sha-256=:3/1gIbsr1bCvZ2KQgJ7DpTGR3YHH9wpLKGiKNiGCmG8=:"
        );
    }

    #[test]
    fn test_sign_request_with_query_param() {
        let mut req = Client::new()
            .get("https://example.com/?param=value")
            .build()
            .unwrap();

        let key_id = "test-key";
        let key_material = "secret";

        // Use the plural @query-params which expands automatically
        // This will internally call resolve_components -> try_from("@query-param;name=\"param\"")
        // If this succeeds, then the logic is correct.
        let components = vec!["@method".to_string(), "@query-params".to_string()];
        sign_request(&mut req, key_id, key_material, Some(&components), None).unwrap();

        let sig_input = req.headers()["signature-input"].to_str().unwrap();
        assert!(sig_input.contains("sig1="));
        // Check that the expanded component is present
        assert!(sig_input.contains("\"@query-param\";name=\"param\""));
    }

    #[test]
    fn test_sign_request_hmac() {
        let mut req = Client::new()
            .post("https://example.com/foo")
            .body("data")
            .build()
            .unwrap();

        let key_id = "test-key";
        let key_material = "secret"; // HMAC key

        // Explicitly include content-digest
        let components = vec![
            "@method".to_string(),
            "@authority".to_string(),
            "content-digest".to_string(),
        ];
        sign_request(&mut req, key_id, key_material, Some(&components), None).unwrap();

        assert!(req.headers().contains_key("signature"));
        assert!(req.headers().contains_key("signature-input"));
        assert!(req.headers().contains_key("content-digest"));

        let sig_input = req.headers()["signature-input"].to_str().unwrap();
        assert!(sig_input.contains("sig1="));
        assert!(sig_input.contains("keyid=\"test-key\""));
        assert!(sig_input.contains("content-digest"));
        assert!(sig_input.contains("alg=\"hmac-sha256\""));
    }

    #[test]
    fn test_bs_parameter_unsupported() {
        let mut req = Client::new()
            .get("https://example.com")
            .header("x-data", "hello")
            .build()
            .unwrap();

        let key_id = "test-key";
        let key_material = "secret";

        // Attempt to sign with the ;bs parameter which is currently unsupported by the underlying library
        let components = vec!["\"x-data\";bs".to_string()];
        let result = sign_request(&mut req, key_id, key_material, Some(&components), None);

        assert!(result.is_err());
        let err_msg = format!("{:?}", result.err().unwrap());
        // The underlying library httpsig currently returns "Not yet implemented: `bs` is not supported yet"
        assert!(err_msg.contains("not supported"));
    }

    #[test]
    fn test_sf_parameter_success() {
        let mut req = Client::new()
            .get("https://example.com")
            .header("x-struct", "a=1, b=2")
            .build()
            .unwrap();

        // ;sf is implemented in the underlying library
        let components = vec!["\"x-struct\";sf".to_string()];
        let result = sign_request(&mut req, "key1", "secret", Some(&components), None);
        assert!(result.is_ok(), "sf parameter should be supported");
    }

    #[test]
    fn test_key_parameter_success() {
        let mut req = Client::new()
            .get("https://example.com")
            .header("x-dict", "a=1, b=2")
            .build()
            .unwrap();

        // ;key is implemented in the underlying library
        let components = vec!["\"x-dict\";key=\"a\"".to_string()];
        let result = sign_request(&mut req, "key1", "secret", Some(&components), None);
        assert!(result.is_ok(), "key parameter should be supported");
    }

    #[test]
    fn test_tr_parameter_unsupported() {
        let mut req = Client::new()
            .get("https://example.com")
            .header("x-field", "value")
            .build()
            .unwrap();

        // ;tr is explicitly NOT implemented in the underlying library
        let components = vec!["\"x-field\";tr".to_string()];
        let result = sign_request(&mut req, "key1", "secret", Some(&components), None);

        assert!(result.is_err());
        let err_msg = format!("{:?}", result.err().unwrap());
        assert!(err_msg.contains("tr") && err_msg.contains("supported"));
    }

    #[test]
    fn test_name_parameter_error_on_field() {
        let mut req = Client::new()
            .get("https://example.com")
            .header("x-field", "value")
            .build()
            .unwrap();

        // ;name is only for @query-param, using it on a regular field should error
        let components = vec!["\"x-field\";name=\"id\"".to_string()];
        let result = sign_request(&mut req, "key1", "secret", Some(&components), None);

        assert!(result.is_err());
        let err_msg = format!("{:?}", result.err().unwrap());
        // It could be either a validation error or a parsing error depending on the library version
        assert!(err_msg.contains("name"));
    }

    #[test]
    fn test_resolve_components_defaults() {
        let req = Client::new().get("http://a.com").build().unwrap();

        let defaults = resolve_components(&req, None);
        assert_eq!(defaults, vec!["@method", "@authority", "@target-uri"]);
    }

    #[test]
    fn test_resolve_components_query_params_deduplicates_names() {
        let req = Client::new()
            .get("https://example.com/?id=1&id=2&name=alice&id=3")
            .build()
            .unwrap();
        let input = vec!["@query-params".to_string()];

        let resolved = resolve_components(&req, Some(&input));
        assert_eq!(
            resolved,
            vec!["@query-param;name=\"id\"", "@query-param;name=\"name\""]
        );
    }

    #[test]
    fn test_duplicate_component_rejected() {
        let components = vec!["@method".to_string(), "@method".to_string()];
        let result = build_signature_params(&components);
        assert!(result.is_err());
        assert!(format!("{:?}", result.err().unwrap()).contains("Duplicate covered component"));
    }

    #[test]
    fn test_equivalent_component_with_different_param_order_rejected() {
        let first = HttpMessageComponentId::try_from("\"x-field\";sf;tr").unwrap();
        let second = HttpMessageComponentId::try_from("\"x-field\";tr;sf").unwrap();
        assert_eq!(
            component_uniqueness_key(&first),
            component_uniqueness_key(&second)
        );

        let components = vec![
            "\"x-field\";sf;tr".to_string(),
            "\"x-field\";tr;sf".to_string(),
        ];
        let result = build_signature_params(&components);
        assert!(result.is_err());
        assert!(format!("{:?}", result.err().unwrap()).contains("Duplicate covered component"));
    }

    #[test]
    fn test_normalize_component_id() {
        // Should wrap @ components with parameters in quotes
        assert_eq!(
            normalize_component_id("@query-param;name=\"a\""),
            "\"@query-param\";name=\"a\""
        );
        // Should not wrap if already wrapped
        assert_eq!(
            normalize_component_id("\"@query-param\";name=\"a\""),
            "\"@query-param\";name=\"a\""
        );
        // Should not wrap regular headers
        assert_eq!(normalize_component_id("content-type"), "content-type");
        // Should not wrap @ components without parameters
        assert_eq!(normalize_component_id("@method"), "@method");
    }

    #[test]
    fn test_invalid_pem_key_does_not_fall_back_to_hmac() {
        let mut req = Client::new().get("https://example.com").build().unwrap();
        let invalid_pem = "-----BEGIN PRIVATE KEY-----\nnot-a-valid-key\n-----END PRIVATE KEY-----";
        let result = sign_request(&mut req, "key1", invalid_pem, None, None);

        assert!(result.is_err());
        let err_msg = format!("{:?}", result.err().unwrap());
        assert!(err_msg.contains("Failed to parse PEM private key"));
        assert!(!req.headers().contains_key("signature"));
    }

    #[test]
    fn test_rsa_pem_requires_explicit_algorithm() {
        let rsa_key_path = format!(
            "{}/tests/fixtures/keys/rsa_private_key_pkcs8.pem",
            env!("CARGO_MANIFEST_DIR")
        );
        let pem = std::fs::read(rsa_key_path).unwrap();
        let result = build_signing_key(&pem, "key1", None);
        assert!(result.is_err());
        let err_msg = format!("{:?}", result.err().unwrap());
        assert!(err_msg.contains("RSA private keys require an explicit algorithm"));
    }

    #[test]
    fn test_rsa_pem_with_explicit_algorithm_succeeds() {
        let rsa_key_path = format!(
            "{}/tests/fixtures/keys/rsa_private_key_pkcs8.pem",
            env!("CARGO_MANIFEST_DIR")
        );
        let pem = std::fs::read(rsa_key_path).unwrap();
        let result = build_signing_key(&pem, "key1", Some(AlgorithmName::RsaV1_5Sha256));
        assert!(result.is_ok());
    }
}
