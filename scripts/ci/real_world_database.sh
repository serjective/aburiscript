#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

aburi_bin="${ABURI_BIN:-${repo_root}/cmake-build-debug/aburi}"
if [[ ! -x "${aburi_bin}" ]]; then
    echo "aburi binary not found or not executable: ${aburi_bin}" >&2
    exit 1
fi

validation_root="${ABURI_VALIDATION_ROOT:-/tmp/aburi-real-world-database-validation}"
source_override_root="${ABURI_SOURCE_OVERRIDE_ROOT:-}"
jobs="${ABURI_JOBS:-$(sysctl -n hw.logicalcpu 2>/dev/null || getconf NPROCESSORS_ONLN 2>/dev/null || echo 4)}"
projects=("$@")

if [[ ${#projects[@]} -eq 0 ]]; then
    projects=(sqlite postgres redis)
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

    local brew_prefix
    brew_prefix="$(brew --prefix 2>/dev/null || true)"
    if [[ -n "${brew_prefix}" && -x "${brew_prefix}/bin/${tool_name}" ]]; then
        echo "${brew_prefix}/bin/${tool_name}"
        return 0
    fi

    if command -v "${tool_name}" >/dev/null 2>&1; then
        command -v "${tool_name}"
        return 0
    fi

    echo "required tool not found on PATH: ${tool_name}" >&2
    exit 1
}

log_step() {
    echo
    echo "==> $*"
}

find_host_cxx() {
    local host_cxx

    host_cxx="${ABURI_HOST_CXX:-$(command -v c++ || true)}"
    if [[ -z "${host_cxx}" ]]; then
        host_cxx="$(find_tool clang++)"
    fi

    echo "${host_cxx}"
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

download_pinned_archive() {
    local archive_url="$1"
    local archive_sha256="$2"
    local dest_dir="$3"
    local archive_dir="${validation_root}/archives"
    local archive_name
    local archive_path
    local actual_sha256
    local curl_bin
    local shasum_bin
    local tar_bin

    mkdir -p "${archive_dir}"
    archive_name="$(basename "${archive_url}")"
    archive_path="${archive_dir}/${archive_name}"
    curl_bin="$(find_tool curl)"
    shasum_bin="$(find_tool shasum)"
    tar_bin="$(find_tool tar)"

    rm -rf "${dest_dir}"
    mkdir -p "${dest_dir}"

    "${curl_bin}" -L --fail --retry 3 --output "${archive_path}" "${archive_url}"
    actual_sha256="$("${shasum_bin}" -a 256 "${archive_path}" | awk '{print $1}')"
    if [[ "${actual_sha256}" != "${archive_sha256}" ]]; then
        echo "sha256 mismatch for ${archive_name}: expected ${archive_sha256}, got ${actual_sha256}" >&2
        exit 1
    fi

    "${tar_bin}" -xzf "${archive_path}" --strip-components=1 -C "${dest_dir}"
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
        sqlite)
            download_pinned_archive \
                "https://sqlite.org/2026/sqlite-autoconf-3510200.tar.gz" \
                "fbd89f866b1403bb66a143065440089dd76100f2238314d92274a082d4f2b7bb" \
                "${dest_dir}"
            ;;
        postgres)
            clone_pinned_repo \
                "https://github.com/postgres/postgres.git" \
                "8b02c22bb43cb480f437704dc547ea77196b7e93" \
                "${dest_dir}"
            ;;
        redis)
            clone_pinned_repo \
                "https://github.com/redis/redis.git" \
                "9accf8bd2459dc0e9eea77dafed0a94381d4f5c2" \
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
        sqlite) echo "3.51.2" ;;
        postgres) echo "8b02c22bb43cb480f437704dc547ea77196b7e93" ;;
        redis) echo "9accf8bd2459dc0e9eea77dafed0a94381d4f5c2" ;;
        *)
            echo "unknown project: $1" >&2
            exit 1
            ;;
    esac
}

run_sqlite() {
    local src_dir="$1"
    local logs_dir="$2"

    log_step "Configuring sqlite"
    (
        cd "${src_dir}"
        CC="${toolchain_dir}/clang" \
        CXX="${toolchain_dir}/clang++" \
            ./configure \
                --disable-dependency-tracking \
                >"${logs_dir}/configure.log" 2>&1
    )

    log_step "Building sqlite"
    (
        cd "${src_dir}"
        make -j"${jobs}" sqlite3 >"${logs_dir}/build.log" 2>&1
    )

    if [[ ! -x "${src_dir}/sqlite3" ]]; then
        echo "sqlite build did not produce sqlite3" >&2
        exit 1
    fi

    log_step "Running sqlite smoke checks"
    (
        cd "${src_dir}"
        ./sqlite3 ':memory:' 'select sqlite_version();' >"${logs_dir}/smoke.log" 2>&1
    )
}

run_postgres() {
    local project_root="$1"
    local src_dir="$2"
    local logs_dir="$3"
    local build_dir="${project_root}/build"
    local make_bin
    local lib_dirs

    make_bin="$(find_tool make)"
    rm -rf "${build_dir}"
    mkdir -p "${build_dir}"

    log_step "Configuring postgres"
    (
        cd "${build_dir}"
        CC="${toolchain_dir}/clang" \
        CXX="${toolchain_dir}/clang++" \
            "${src_dir}/configure" \
                --without-readline \
                --without-zlib \
                --without-icu \
                >"${logs_dir}/configure.log" 2>&1
    )

    log_step "Building postgres"
    (
        cd "${build_dir}"
        "${make_bin}" -j1 -C src/bin/psql psql >"${logs_dir}/build.log" 2>&1
    )

    if [[ ! -x "${build_dir}/src/bin/psql/psql" ]]; then
        echo "postgres build did not produce psql" >&2
        exit 1
    fi

    lib_dirs="${build_dir}/src/interfaces/libpq:${build_dir}/src/common:${build_dir}/src/port"

    log_step "Running postgres smoke checks"
    (
        cd "${build_dir}"
        DYLD_LIBRARY_PATH="${lib_dirs}" \
            ./src/bin/psql/psql --version >"${logs_dir}/smoke.log" 2>&1
    )
}

run_redis() {
    local project_root="$1"
    local src_dir="$2"
    local logs_dir="$3"
    local make_bin
    local runtime_dir="${project_root}/runtime"
    local redis_port="$((19000 + ($$ % 1000)))"
    local pidfile_path="${runtime_dir}/redis.pid"
    local logfile_path="${runtime_dir}/redis.log"
    local host_cxx

    make_bin="$(find_tool make)"
    host_cxx="$(find_host_cxx)"

    log_step "Preparing redis"
    (
        cd "${src_dir}"
        {
            echo "redis uses direct make-based builds"
            "${make_bin}" distclean || true
        } >"${logs_dir}/configure.log" 2>&1
    )

    log_step "Building redis"
    (
        cd "${src_dir}"
        "${make_bin}" -j"${jobs}" \
            CC="${toolchain_dir}/clang" \
            CXX="${host_cxx}" \
            MALLOC=libc \
            BUILD_TLS=no \
            >"${logs_dir}/build.log" 2>&1
    )

    if [[ ! -x "${src_dir}/src/redis-server" || ! -x "${src_dir}/src/redis-cli" ]]; then
        echo "redis build did not produce redis-server and redis-cli" >&2
        exit 1
    fi

    mkdir -p "${runtime_dir}"
    rm -f "${pidfile_path}" "${logfile_path}"

    log_step "Running redis smoke checks"
    (
        cd "${src_dir}"

        cleanup() {
            if [[ -x ./src/redis-cli ]]; then
                ./src/redis-cli -h 127.0.0.1 -p "${redis_port}" shutdown nosave >/dev/null 2>&1 || true
            fi
        }
        trap cleanup EXIT

        {
            ./src/redis-server --version
            ./src/redis-cli --version
            ./src/redis-server \
                --port "${redis_port}" \
                --save "" \
                --appendonly no \
                --daemonize yes \
                --bind 127.0.0.1 \
                --pidfile "${pidfile_path}" \
                --logfile "${logfile_path}" \
                --dir "${runtime_dir}"

            for _ in $(seq 1 50); do
                if ./src/redis-cli -h 127.0.0.1 -p "${redis_port}" ping >/dev/null 2>&1; then
                    break
                fi
                sleep 0.1
            done

            ./src/redis-cli -h 127.0.0.1 -p "${redis_port}" ping
        } >"${logs_dir}/smoke.log" 2>&1
    )
}

run_project() {
    local project="$1"
    local project_root
    local src_dir
    local logs_dir
    local project_label

    project_root="${validation_root}/${project}"
    src_dir="${project_root}/src"
    logs_dir="${project_root}/logs"
    project_label="$(project_ref "${project}")"

    rm -rf "${project_root}"
    mkdir -p "${logs_dir}"

    log_step "Fetching ${project} @ ${project_label}"
    populate_source_tree "${project}" "${src_dir}" >"${logs_dir}/fetch.log" 2>&1

    case "${project}" in
        sqlite)
            run_sqlite "${src_dir}" "${logs_dir}"
            ;;
        postgres)
            run_postgres "${project_root}" "${src_dir}" "${logs_dir}"
            ;;
        redis)
            run_redis "${project_root}" "${src_dir}" "${logs_dir}"
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
