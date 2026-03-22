#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

aburi_bin="${ABURI_BIN:-${repo_root}/cmake-build-debug/aburi}"
if [[ ! -x "${aburi_bin}" ]]; then
    echo "aburi binary not found or not executable: ${aburi_bin}" >&2
    exit 1
fi

validation_root="${ABURI_VALIDATION_ROOT:-/tmp/aburi-real-world-compilers-validation}"
source_override_root="${ABURI_SOURCE_OVERRIDE_ROOT:-}"
jobs="${ABURI_JOBS:-$(sysctl -n hw.logicalcpu 2>/dev/null || getconf NPROCESSORS_ONLN 2>/dev/null || echo 4)}"
projects=("$@")

if [[ ${#projects[@]} -eq 0 ]]; then
    projects=(chibicc)
fi

mkdir -p "${validation_root}"
toolchain_dir="${validation_root}/toolchain"
mkdir -p "${toolchain_dir}"

export ABURI_BIN="${aburi_bin}"
ln -sf "${repo_root}/scripts/ci/aburi-toolchain.sh" "${toolchain_dir}/clang"
ln -sf "${repo_root}/scripts/ci/aburi-toolchain.sh" "${toolchain_dir}/clang++"

export PATH="${toolchain_dir}:${PATH}"

if [[ -d "/opt/homebrew/bin" ]]; then
    export PATH="/opt/homebrew/bin:${PATH}"
fi

if [[ -d "/usr/local/bin" ]]; then
    export PATH="/usr/local/bin:${PATH}"
fi

log_step() {
    echo
    echo "==> $*"
}

find_tool() {
    local tool_name="$1"
    if [[ -x "/opt/homebrew/bin/${tool_name}" ]]; then
        echo "/opt/homebrew/bin/${tool_name}"
        return 0
    fi

    if [[ -x "/opt/homebrew/opt/${tool_name}/bin/${tool_name}" ]]; then
        echo "/opt/homebrew/opt/${tool_name}/bin/${tool_name}"
        return 0
    fi

    if [[ -x "/usr/local/bin/${tool_name}" ]]; then
        echo "/usr/local/bin/${tool_name}"
        return 0
    fi

    if [[ -x "/usr/local/opt/${tool_name}/bin/${tool_name}" ]]; then
        echo "/usr/local/opt/${tool_name}/bin/${tool_name}"
        return 0
    fi

    if command -v "${tool_name}" >/dev/null 2>&1; then
        command -v "${tool_name}"
        return 0
    fi

    echo "required tool not found on PATH: ${tool_name}" >&2
    exit 1
}

clone_pinned_repo() {
    local repo_url="$1"
    local repo_ref="$2"
    local dest_dir="$3"

    rm -rf "${dest_dir}"
    mkdir -p "${dest_dir}"
    git init -q "${dest_dir}"
    git -C "${dest_dir}" remote add origin "${repo_url}"
    git -C "${dest_dir}" fetch --depth=1 origin "${repo_ref}"
    git -C "${dest_dir}" checkout --detach -q FETCH_HEAD
}

populate_source_tree() {
    local project="$1"
    local dest_dir="$2"

    if [[ -n "${source_override_root}" && -d "${source_override_root}/${project}" ]]; then
        rm -rf "${dest_dir}"
        mkdir -p "${dest_dir}"
        cp -R "${source_override_root}/${project}/." "${dest_dir}"
        return 0
    fi

    case "${project}" in
        chibicc)
            clone_pinned_repo \
                "https://github.com/rui314/chibicc.git" \
                "90d1f7f199cc55b13c7fdb5839d1409806633fdb" \
                "${dest_dir}"
            ;;
        *)
            echo "unknown project: ${project}" >&2
            exit 1
            ;;
    esac
}

project_ref() {
    case "$1" in
        chibicc) echo "90d1f7f199cc55b13c7fdb5839d1409806633fdb" ;;
        *)
            echo "unknown project: $1" >&2
            exit 1
            ;;
    esac
}

run_chibicc() {
    local project_root="$1"
    local src_dir="$2"
    local logs_dir="$3"
    local smoke_src="${project_root}/smoke.c"
    local smoke_asm="${project_root}/smoke.s"
    local make_bin

    make_bin="$(find_tool make)"

    log_step "Cleaning chibicc tree"
    (
        cd "${src_dir}"
        "${make_bin}" clean >"${logs_dir}/clean.log" 2>&1 || true
    )

    log_step "Building chibicc"
    (
        cd "${src_dir}"
        "${make_bin}" -j"${jobs}" CC="${toolchain_dir}/clang" chibicc >"${logs_dir}/build.log" 2>&1
    )

    if [[ ! -x "${src_dir}/chibicc" ]]; then
        echo "chibicc build did not produce chibicc" >&2
        exit 1
    fi

    printf '%s\n' 'int main(void) { return 67; }' > "${smoke_src}"

    log_step "Running chibicc smoke checks"
    (
        cd "${src_dir}"
        ./chibicc -S -o "${smoke_asm}" "${smoke_src}" >"${logs_dir}/smoke.log" 2>&1
    )

    if [[ ! -s "${smoke_asm}" ]]; then
        echo "chibicc smoke check did not produce assembly output" >&2
        exit 1
    fi

    if ! grep -q "main:" "${smoke_asm}"; then
        echo "chibicc smoke assembly does not contain a main label" >&2
        exit 1
    fi
}

run_project() {
    local project="$1"
    local repo_ref
    local project_root
    local src_dir
    local logs_dir

    repo_ref="$(project_ref "${project}")"
    project_root="${validation_root}/${project}"
    src_dir="${project_root}/src"
    logs_dir="${project_root}/logs"

    rm -rf "${project_root}"
    mkdir -p "${logs_dir}"

    log_step "Fetching ${project} @ ${repo_ref}"
    populate_source_tree "${project}" "${src_dir}" >"${logs_dir}/fetch.log" 2>&1

    case "${project}" in
        chibicc)
            run_chibicc "${project_root}" "${src_dir}" "${logs_dir}"
            ;;
        *)
            echo "unknown project: ${project}" >&2
            exit 1
            ;;
    esac

    echo "${project} validation passed"
}

for project in "${projects[@]}"; do
    run_project "${project}"
done
