#!/usr/bin/env bash

set -euo pipefail

if ! command -v brew >/dev/null 2>&1; then
    echo "Homebrew is required on macOS runners." >&2
    exit 1
fi

brew_prefix="$(brew --prefix)"
export PATH="${brew_prefix}/bin:${PATH}"

packages=(
    bison
    flex
    glib
    llvm@18
    meson
    ninja
    orc
    pkg-config
)

for package in "${packages[@]}"; do
    if ! brew list --versions "${package}" >/dev/null 2>&1; then
        brew install "${package}"
    fi
done

python3 -m pip install --user --disable-pip-version-check jinja2
