#!/bin/sh
# Generate man page and completions
set -e
cd "$(dirname "$0")"

XH_HELP2MAN=1 help2man \
  --include 'doc/man-template.roff' \
  --help-option 'help' \
  --version-option '-V' \
  --name 'Friendly and fast tool for sending HTTP requests' \
  --output 'doc/xh.1' \
  --no-info \
  'cargo run --all-features --'

cargo run --all-features -- generate_completions completions

# Subcommand check is unnecessary: https://github.com/clap-rs/clap/pull/2359
sed 's/ -n "__fish_use_subcommand"//g' completions/xh.fish > completions/xh.fish.new
mv completions/xh.fish.new completions/xh.fish
