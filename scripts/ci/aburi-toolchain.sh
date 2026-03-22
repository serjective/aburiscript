#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
aburi_bin="${ABURI_BIN:-${repo_root}/cmake-build-debug/aburi}"

if [[ ! -x "${aburi_bin}" ]]; then
    echo "aburi binary not found or not executable: ${aburi_bin}" >&2
    exit 1
fi

tool_name="$(basename "$0")"
driver_args=(--ignore-unknown-options --driver-persona=clang)
extra_args=()
has_lang_flag=false
has_stdin_input=false

for arg in "$@"; do
    if [[ "${arg}" == "-x" ]]; then
        has_lang_flag=true
    fi
    if [[ "${arg}" == "-" ]]; then
        has_stdin_input=true
    fi
done

if [[ "${has_lang_flag}" == false && "${has_stdin_input}" == true ]]; then
    if [[ "${tool_name}" == *"++" ]]; then
        extra_args=(-x c++)
    else
        extra_args=(-x c)
    fi
fi

cmd=( "${aburi_bin}" "${driver_args[@]}" )
if [[ ${#extra_args[@]} -gt 0 ]]; then
    cmd+=( "${extra_args[@]}" )
fi

if [[ "${tool_name}" == *"++" ]]; then
    cmd+=( -x c++ "$@" )
    exec "${cmd[@]}"
fi

cmd+=( "$@" )
exec "${cmd[@]}"
