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
    ffmpeg
    flex
    glib
    libass
    libplacebo
    llvm
    meson
    ninja
    orc
    pkg-config
    z3
    zstd
)

for package in "${packages[@]}"; do
    if ! brew list --versions "${package}" >/dev/null 2>&1; then
        brew install "${package}"
    fi
done
