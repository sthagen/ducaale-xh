use std::{fs::File, io, path::Path, str::FromStr};

use anyhow::{anyhow, Result};
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};
use reqwest::{blocking::multipart, Method};
use structopt::clap;

use crate::cli::RequestType;

pub const FORM_CONTENT_TYPE: &str = "application/x-www-form-urlencoded";
pub const JSON_CONTENT_TYPE: &str = "application/json";
pub const JSON_ACCEPT: &str = "application/json, */*;q=0.5";

#[derive(Debug, Clone, PartialEq)]
pub enum RequestItem {
    HttpHeader(String, String),
    HttpHeaderToUnset(String),
    UrlParam(String, String),
    DataField(String, String),
    JSONField(String, serde_json::Value),
    FormFile(String, String, Option<String>),
}

impl FromStr for RequestItem {
    type Err = clap::Error;
    fn from_str(request_item: &str) -> clap::Result<RequestItem> {
        const SPECIAL_CHARS: &str = "=@:;\\";
        const SEPS: &[&str] = &["==", ":=", "=", "@", ":"];

        fn unescape(text: &str) -> String {
            let mut out = String::new();
            let mut chars = text.chars();
            while let Some(ch) = chars.next() {
                if ch == '\\' {
                    match chars.next() {
                        Some(next) if SPECIAL_CHARS.contains(next) => {
                            // Escape this character
                            out.push(next);
                        }
                        Some(next) => {
                            // Do not escape this character, treat backslash
                            // as ordinary character
                            out.push(ch);
                            out.push(next);
                        }
                        None => {
                            out.push(ch);
                        }
                    }
                } else {
                    out.push(ch);
                }
            }
            out
        }

        fn split(request_item: &str) -> Option<(String, &'static str, String)> {
            let mut char_inds = request_item.char_indices();
            while let Some((ind, ch)) = char_inds.next() {
                if ch == '\\' {
                    // If the next character is special it's escaped and can't be
                    // the start of the separator
                    // And if it's normal it can't be the start either
                    // Just skip it without looking
                    char_inds.next();
                    continue;
                }
                for sep in SEPS {
                    if let Some(value) = request_item[ind..].strip_prefix(sep) {
                        let key = &request_item[..ind];
                        return Some((unescape(key), sep, unescape(value)));
                    }
                }
            }
            None
        }

        if let Some((key, sep, value)) = split(request_item) {
            match sep {
                "==" => Ok(RequestItem::UrlParam(key, value)),
                "=" => Ok(RequestItem::DataField(key, value)),
                ":=" => Ok(RequestItem::JSONField(
                    key,
                    serde_json::from_str(&value).map_err(|err| {
                        clap::Error::with_description(
                            &format!("{:?}: {}", request_item, err),
                            clap::ErrorKind::InvalidValue,
                        )
                    })?,
                )),
                "@" => {
                    // Technically there are concerns about escaping but people
                    // probably don't put ;type= in their filenames often
                    let with_type: Vec<&str> = value.rsplitn(2, ";type=").collect();
                    // rsplitn iterates from the right, so it's either
                    if let Some(&typed_filename) = with_type.get(1) {
                        // [mimetype, filename]
                        Ok(RequestItem::FormFile(
                            key,
                            typed_filename.to_owned(),
                            Some(with_type[0].to_owned()),
                        ))
                    } else {
                        // [filename]
                        Ok(RequestItem::FormFile(key, value, None))
                    }
                }
                ":" if value.is_empty() => Ok(RequestItem::HttpHeaderToUnset(key)),
                ":" => Ok(RequestItem::HttpHeader(key, value)),
                _ => unreachable!(),
            }
        } else if let Some(header) = request_item.strip_suffix(';') {
            // Technically this is too permissive because the ; might be escaped
            Ok(RequestItem::HttpHeader(header.to_owned(), "".to_owned()))
        } else {
            // TODO: We can also end up here if the method couldn't be parsed
            // and was interpreted as a URL, making the actual URL a request
            // item
            Err(clap::Error::with_description(
                &format!("{:?} is not a valid request item", request_item),
                clap::ErrorKind::InvalidValue,
            ))
        }
    }
}

pub struct RequestItems(pub Vec<RequestItem>);

pub enum Body {
    Json(serde_json::Map<String, serde_json::Value>),
    Form(Vec<(String, String)>),
    Multipart(multipart::Form),
    Raw(Vec<u8>),
}

impl Body {
    pub fn is_empty(&self) -> bool {
        match self {
            Body::Json(map) => map.is_empty(),
            Body::Form(items) => items.is_empty(),
            Body::Raw(data) => data.is_empty(),
            // A multipart form without items isn't empty, and we can't read
            // a body from stdin because it has to match the header, so we
            // should never consider this "empty"
            // This is a slight divergence from HTTPie, which will simply
            // discard stdin if it receives --multipart without request items,
            // but that behavior is useless so there's no need to match it
            Body::Multipart(_) => false,
        }
    }

    pub fn pick_method(&self) -> Method {
        if self.is_empty() {
            Method::GET
        } else {
            Method::POST
        }
    }

    pub fn is_multipart(&self) -> bool {
        matches!(self, Body::Multipart(..))
    }
}

impl RequestItems {
    pub fn new(request_items: Vec<RequestItem>) -> RequestItems {
        RequestItems(request_items)
    }

    pub fn has_form_files(&self) -> bool {
        self.0
            .iter()
            .any(|item| matches!(item, RequestItem::FormFile(..)))
    }

    pub fn headers(&self) -> Result<(HeaderMap<HeaderValue>, Vec<HeaderName>)> {
        let mut headers = HeaderMap::new();
        let mut headers_to_unset = vec![];
        for item in &self.0 {
            match item {
                RequestItem::HttpHeader(key, value) => {
                    let key = HeaderName::from_bytes(&key.as_bytes())?;
                    let value = HeaderValue::from_str(&value)?;
                    headers.insert(key, value);
                }
                RequestItem::HttpHeaderToUnset(key) => {
                    let key = HeaderName::from_bytes(&key.as_bytes())?;
                    headers_to_unset.push(key);
                }
                _ => {}
            }
        }
        Ok((headers, headers_to_unset))
    }

    pub fn query(&self) -> Vec<(&str, &str)> {
        let mut query = vec![];
        for item in &self.0 {
            if let RequestItem::UrlParam(key, value) = item {
                query.push((key.as_str(), value.as_str()));
            }
        }
        query
    }

    fn body_as_json(self) -> Result<Body> {
        let mut body = serde_json::Map::new();
        for item in self.0 {
            match item {
                RequestItem::JSONField(key, value) => {
                    body.insert(key, value);
                }
                RequestItem::DataField(key, value) => {
                    body.insert(key, serde_json::Value::String(value));
                }
                RequestItem::FormFile(_, _, _) => {
                    return Err(anyhow!(
                        "Sending Files is not supported when the request body is in JSON format"
                    ));
                }
                _ => {}
            }
        }
        Ok(Body::Json(body))
    }

    fn body_as_form(self) -> Result<Body> {
        let mut text_fields = Vec::<(String, String)>::new();
        for item in self.0 {
            match item {
                RequestItem::JSONField(_, _) => {
                    return Err(anyhow!("JSON values are not supported in Form fields"));
                }
                RequestItem::DataField(key, value) => text_fields.push((key, value)),
                RequestItem::FormFile(..) => unreachable!(),
                _ => {}
            }
        }
        Ok(Body::Form(text_fields))
    }

    fn body_as_multipart(self) -> Result<Body> {
        let mut form = multipart::Form::new();
        for item in self.0 {
            match item {
                RequestItem::JSONField(_, _) => {
                    return Err(anyhow!("JSON values are not supported in multipart fields"));
                }
                RequestItem::DataField(key, value) => {
                    form = form.text(key, value);
                }
                RequestItem::FormFile(key, value, file_type) => {
                    let mut part = file_to_part(&value)?;
                    if let Some(file_type) = file_type {
                        part = part.mime_str(&file_type)?;
                    }
                    form = form.part(key, part);
                }
                _ => {}
            }
        }
        Ok(Body::Multipart(form))
    }

    pub fn body(self, request_type: Option<RequestType>) -> Result<Body> {
        match request_type {
            Some(RequestType::Multipart) => self.body_as_multipart(),
            Some(RequestType::Form) if self.has_form_files() => self.body_as_multipart(),
            Some(RequestType::Form) => self.body_as_form(),
            Some(RequestType::Json) | None => self.body_as_json(),
        }
    }

    /// Guess which would be appropriate for the return value of `body`.
    ///
    /// It's better to use `Body::pick_method`, if possible. This method is
    /// for the benefit of `to_curl`, which sometimes has to process the
    /// request items itself.
    pub fn pick_method(&self, request_type: Option<RequestType>) -> Method {
        if request_type == Some(RequestType::Multipart) {
            return Method::POST;
        }
        for item in &self.0 {
            match item {
                RequestItem::HttpHeader(..)
                | RequestItem::HttpHeaderToUnset(..)
                | RequestItem::UrlParam(..) => continue,
                RequestItem::DataField(..)
                | RequestItem::JSONField(..)
                | RequestItem::FormFile(..) => return Method::POST,
            }
        }
        Method::GET
    }
}

pub fn file_to_part(path: impl AsRef<Path>) -> io::Result<multipart::Part> {
    let path = path.as_ref();
    let file_name = path
        .file_name()
        .map(|file_name| file_name.to_string_lossy().to_string());
    let file = File::open(path)?;
    let file_length = file.metadata()?.len();
    let mut part = multipart::Part::reader_with_length(file, file_length);
    if let Some(file_name) = file_name {
        part = part.file_name(file_name);
    }
    Ok(part)
}

#[cfg(test)]
mod tests {
    use super::*;

    use serde_json::json;

    #[test]
    fn request_item_parsing() {
        use serde_json::json;

        use RequestItem::*;

        fn parse(text: &str) -> RequestItem {
            text.parse().unwrap()
        }

        // Data field
        assert_eq!(parse("foo=bar"), DataField("foo".into(), "bar".into()));
        // URL param
        assert_eq!(parse("foo==bar"), UrlParam("foo".into(), "bar".into()));
        // Escaped right before separator
        assert_eq!(parse(r"foo\==bar"), DataField("foo=".into(), "bar".into()));
        // Header
        assert_eq!(parse("foo:bar"), HttpHeader("foo".into(), "bar".into()));
        // JSON field
        assert_eq!(parse("foo:=[1,2]"), JSONField("foo".into(), json!([1, 2])));
        // Bad JSON field
        "foo:=bar".parse::<RequestItem>().unwrap_err();
        // Can't escape normal chars
        assert_eq!(
            parse(r"f\o\o=\ba\r"),
            DataField(r"f\o\o".into(), r"\ba\r".into()),
        );
        // Can escape special chars
        assert_eq!(
            parse(r"f\=\:\@\;oo=b\:\:\:ar"),
            DataField("f=:@;oo".into(), "b:::ar".into()),
        );
        // Unset header
        assert_eq!(parse("foobar:"), HttpHeaderToUnset("foobar".into()));
        // Empty header
        assert_eq!(parse("foobar;"), HttpHeader("foobar".into(), "".into()));
        // Untyped file
        assert_eq!(parse("foo@bar"), FormFile("foo".into(), "bar".into(), None));
        // Typed file
        assert_eq!(
            parse("foo@bar;type=qux"),
            FormFile("foo".into(), "bar".into(), Some("qux".into())),
        );
        // Multi-typed file
        assert_eq!(
            parse("foo@bar;type=qux;type=qux"),
            FormFile("foo".into(), "bar;type=qux".into(), Some("qux".into())),
        );
        // Empty filename
        // (rejecting this would be fine too, the main point is to see if it panics)
        assert_eq!(parse("foo@"), FormFile("foo".into(), "".into(), None));
        // No separator
        "foobar".parse::<RequestItem>().unwrap_err();
        "".parse::<RequestItem>().unwrap_err();
        // Trailing backslash
        assert_eq!(parse(r"foo=bar\"), DataField("foo".into(), r"bar\".into()));
        // Escaped backslash
        assert_eq!(parse(r"foo\\=bar"), DataField(r"foo\".into(), "bar".into()),);
        // Unicode
        assert_eq!(
            parse("\u{00B5}=\u{00B5}"),
            DataField("\u{00B5}".into(), "\u{00B5}".into()),
        );
        // Empty
        assert_eq!(parse("="), DataField("".into(), "".into()));
    }
}
