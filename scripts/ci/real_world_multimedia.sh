#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

aburi_bin="${ABURI_BIN:-${repo_root}/cmake-build-debug/aburi}"
if [[ ! -x "${aburi_bin}" ]]; then
    echo "aburi binary not found or not executable: ${aburi_bin}" >&2
    exit 1
fi

validation_root="${ABURI_VALIDATION_ROOT:-/tmp/aburi-real-world-validation}"
source_override_root="${ABURI_SOURCE_OVERRIDE_ROOT:-}"
jobs="${ABURI_JOBS:-$(sysctl -n hw.logicalcpu 2>/dev/null || getconf NPROCESSORS_ONLN 2>/dev/null || echo 4)}"
projects=("$@")

if [[ ${#projects[@]} -eq 0 ]]; then
    projects=(ffmpeg librempeg libplacebo mpv gstreamer ghostscript)
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

    case "${archive_name}" in
        *.tar.gz|*.tgz)
            "${tar_bin}" -xzf "${archive_path}" --strip-components=1 -C "${dest_dir}"
            ;;
        *.tar.xz)
            "${tar_bin}" -xJf "${archive_path}" --strip-components=1 -C "${dest_dir}"
            ;;
        *)
            echo "unsupported archive format: ${archive_name}" >&2
            exit 1
            ;;
    esac
}

populate_source_tree() {
    local project="$1"
    local repo_url="$2"
    local repo_ref="$3"
    local dest_dir="$4"

    if [[ -n "${source_override_root}" && -d "${source_override_root}/${project}" ]]; then
        rm -rf "${dest_dir}"
        mkdir -p "${dest_dir}"
        cp -R "${source_override_root}/${project}/." "${dest_dir}"
        return 0
    fi

    if [[ "${project}" == "ghostscript" ]]; then
        download_pinned_archive \
            "${repo_url}" \
            "3602056368cf649026231e2d65250b5860c023f3d4a0d9c35e6605e28e543ec1" \
            "${dest_dir}"
        return 0
    fi

    clone_pinned_repo "${repo_url}" "${repo_ref}" "${dest_dir}"
}

project_repo() {
    case "$1" in
        ffmpeg) echo "https://github.com/FFmpeg/ffmpeg.git" ;;
        librempeg) echo "https://github.com/librempeg/librempeg.git" ;;
        libplacebo) echo "https://github.com/haasn/libplacebo.git" ;;
        mpv) echo "https://github.com/mpv-player/mpv.git" ;;
        gstreamer) echo "https://gitlab.freedesktop.org/gstreamer/gstreamer.git" ;;
        ghostscript) echo "https://github.com/ArtifexSoftware/ghostpdl-downloads/releases/download/gs10060/ghostpdl-10.06.0.tar.xz" ;;
        *)
            echo "unknown project: $1" >&2
            exit 1
            ;;
    esac
}

project_ref() {
    case "$1" in
        ffmpeg) echo "33b215d1554a14e87416a24f8e6034312e629af7" ;;
        librempeg) echo "7167113fbdbce844d44b6af73708720d2d9743fe" ;;
        libplacebo) echo "33b5dfada6a84692912e4d41f673f895df79479e" ;;
        mpv) echo "7b1ee864b83e6fe89f936f13b1c5ae34048432b9" ;;
        gstreamer) echo "1167f89c431263eb63830ef7fd3d10b22b7ea793" ;;
        ghostscript) echo "10.06.0" ;;
        *)
            echo "unknown project: $1" >&2
            exit 1
            ;;
    esac
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

find_host_clang() {
    if [[ -n "${ABURI_HOST_CC:-}" ]]; then
        echo "${ABURI_HOST_CC}"
        return 0
    fi

    if [[ -x "/usr/bin/clang" ]]; then
        echo "/usr/bin/clang"
        return 0
    fi

    if command -v xcrun >/dev/null 2>&1; then
        local xcrun_clang
        xcrun_clang="$(xcrun --find clang 2>/dev/null || true)"
        if [[ -n "${xcrun_clang}" ]]; then
            echo "${xcrun_clang}"
            return 0
        fi
    fi

    find_tool clang
}

find_host_clangxx() {
    if [[ -n "${ABURI_HOST_CXX_CLANG:-}" ]]; then
        echo "${ABURI_HOST_CXX_CLANG}"
        return 0
    fi

    if [[ -x "/usr/bin/clang++" ]]; then
        echo "/usr/bin/clang++"
        return 0
    fi

    if command -v xcrun >/dev/null 2>&1; then
        local xcrun_clangxx
        xcrun_clangxx="$(xcrun --find clang++ 2>/dev/null || true)"
        if [[ -n "${xcrun_clangxx}" ]]; then
            echo "${xcrun_clangxx}"
            return 0
        fi
    fi

    find_tool clang++
}

populate_tool_dir() {
    local target_dir="$1"
    shift

    rm -rf "${target_dir}"
    mkdir -p "${target_dir}"

    local tool_name
    local tool_path
    for tool_name in "$@"; do
        tool_path="$(find_tool "${tool_name}")"
        ln -sf "${tool_path}" "${target_dir}/${tool_name}"
    done
}

write_meson_native_file() {
    local native_file="$1"
    local c_compiler="$2"
    local cpp_compiler="$3"
    local objc_compiler="$4"
    local objcpp_compiler="$5"
    local pkg_config_bin="$6"
    local python_bin="$7"
    local bison_bin="$8"
    local flex_bin="$9"

    cat >"${native_file}" <<EOF
[binaries]
c = '${c_compiler}'
cpp = '${cpp_compiler}'
objc = '${objc_compiler}'
objcpp = '${objcpp_compiler}'
pkg-config = '${pkg_config_bin}'
python = '${python_bin}'
bison = '${bison_bin}'
flex = '${flex_bin}'
EOF
}

run_ffmpeg() {
    local src_dir="$1"
    local logs_dir="$2"

    log_step "Configuring FFmpeg"
    (
        cd "${src_dir}"
        ./configure \
            --cc="${toolchain_dir}/clang" \
            --cxx="${toolchain_dir}/clang++" \
            --disable-autodetect \
            --disable-asm \
            --disable-doc \
            >"${logs_dir}/configure.log" 2>&1
    )

    log_step "Building FFmpeg"
    (
        cd "${src_dir}"
        make -j"${jobs}" ffmpeg ffprobe >"${logs_dir}/build.log" 2>&1
    )

    if [[ ! -x "${src_dir}/ffmpeg" || ! -x "${src_dir}/ffprobe" ]]; then
        echo "FFmpeg build did not produce ffmpeg and ffprobe" >&2
        exit 1
    fi

    log_step "Running FFmpeg smoke checks"
    (
        cd "${src_dir}"
        ./ffmpeg -version >"${logs_dir}/smoke.log" 2>&1
        ./ffprobe -version >>"${logs_dir}/smoke.log" 2>&1
    )
}

run_librempeg() {
    local src_dir="$1"
    local logs_dir="$2"

    log_step "Configuring librempeg"
    (
        cd "${src_dir}"
        ./configure \
            --cc="${toolchain_dir}/clang" \
            --cxx="${toolchain_dir}/clang++" \
            --disable-autodetect \
            --disable-asm \
            --disable-doc \
            >"${logs_dir}/configure.log" 2>&1
    )

    log_step "Building librempeg"
    (
        cd "${src_dir}"
        make -j"${jobs}" all >"${logs_dir}/build.log" 2>&1
    )

    if [[ ! -x "${src_dir}/ffprobe" ]]; then
        echo "librempeg build did not produce ffprobe" >&2
        exit 1
    fi

    log_step "Running librempeg smoke checks"
    (
        cd "${src_dir}"
        ./ffprobe -version >"${logs_dir}/smoke.log" 2>&1
        if [[ -x ./ffmpeg ]]; then
            ./ffmpeg -version >>"${logs_dir}/smoke.log" 2>&1
        fi
    )
}

run_libplacebo() {
    local project_root="$1"
    local src_dir="$2"
    local logs_dir="$3"
    local build_dir="${project_root}/build"
    local python_venv_dir="${project_root}/python-venv"
    local native_file="${project_root}/libplacebo-native.ini"
    local meson_bin
    local ninja_bin
    local python_bin
    local host_cxx

    meson_bin="$(find_tool meson)"
    ninja_bin="$(find_tool ninja)"
    python_bin="$(find_tool python3)"
    host_cxx="$(find_host_cxx)"

    log_step "Preparing libplacebo Python environment"
    "${python_bin}" -m venv "${python_venv_dir}" >"${logs_dir}/python-deps.log" 2>&1
    "${python_venv_dir}/bin/python3" -m pip install --disable-pip-version-check jinja2 >>"${logs_dir}/python-deps.log" 2>&1
    cat > "${native_file}" <<EOF
[binaries]
python = '${python_venv_dir}/bin/python3'
EOF

    log_step "Configuring libplacebo"
    PATH="${python_venv_dir}/bin:${PATH}" \
    CC="${toolchain_dir}/clang" \
    CXX="${host_cxx}" \
        "${meson_bin}" setup "${build_dir}" "${src_dir}" \
            --backend=ninja \
            --native-file "${native_file}" \
            --buildtype=debugoptimized \
            -Ddemos=false \
            -Dtests=false \
            -Dbench=false \
            -Dfuzz=false \
            -Dvulkan=disabled \
            -Dopengl=disabled \
            -Dd3d11=disabled \
            -Dglslang=disabled \
            -Dshaderc=disabled \
            -Dlcms=disabled \
            -Ddovi=disabled \
            -Dlibdovi=disabled \
            -Dunwind=disabled \
            -Dxxhash=disabled \
            >"${logs_dir}/configure.log" 2>&1

    log_step "Building libplacebo"
    PATH="${python_venv_dir}/bin:${PATH}" \
        "${ninja_bin}" -C "${build_dir}" >"${logs_dir}/build.log" 2>&1

    if ! find "${build_dir}/src" -maxdepth 1 -name 'libplacebo*.dylib' | grep -q .; then
        echo "libplacebo build did not produce a dylib" >&2
        exit 1
    fi

    find "${build_dir}/src" -maxdepth 1 -name 'libplacebo*.dylib' | sort >"${logs_dir}/artifacts.log"
}

run_mpv() {
    local project_root="$1"
    local src_dir="$2"
    local logs_dir="$3"
    local build_dir="${project_root}/build"
    local meson_bin
    local ninja_bin
    local host_cxx

    meson_bin="$(find_tool meson)"
    ninja_bin="$(find_tool ninja)"
    host_cxx="$(find_host_cxx)"

    log_step "Configuring mpv"
    CC="${toolchain_dir}/clang" \
    CXX="${host_cxx}" \
        "${meson_bin}" setup "${build_dir}" "${src_dir}" \
            --backend=ninja \
            --buildtype=debugoptimized \
            -Dcplayer=true \
            -Dlibmpv=false \
            -Dtests=false \
            -Dfuzzers=false \
            -Dmanpage-build=disabled \
            -Dhtml-build=disabled \
            -Dpdf-build=disabled \
            -Djavascript=disabled \
            -Dlua=disabled \
            -Dvapoursynth=disabled \
            -Dlibarchive=disabled \
            -Dlibbluray=disabled \
            -Ddvdnav=disabled \
            -Dcdda=disabled \
            -Ddvbin=disabled \
            -Djpeg=disabled \
            -Dlcms2=disabled \
            -Drubberband=disabled \
            -Duchardet=disabled \
            -Dzimg=disabled \
            -Dzlib=disabled \
            -Dlibavdevice=disabled \
            -Dshaderc=disabled \
            -Dspirv-cross=disabled \
            -Dvulkan=disabled \
            -Dx11=disabled \
            -Dwayland=disabled \
            -Ddrm=disabled \
            -Dgbm=disabled \
            -Dvaapi=disabled \
            -Dvdpau=disabled \
            -Dcoreaudio=disabled \
            -Davfoundation=disabled \
            -Dcocoa=disabled \
            -Dgl=disabled \
            -Dgl-cocoa=disabled \
            -Dvideotoolbox-gl=disabled \
            -Dvideotoolbox-pl=disabled \
            -Dswift-build=disabled \
            >"${logs_dir}/configure.log" 2>&1

    log_step "Building mpv"
    "${ninja_bin}" -C "${build_dir}" mpv >"${logs_dir}/build.log" 2>&1

    if [[ ! -x "${build_dir}/mpv" ]]; then
        echo "mpv build did not produce the mpv executable" >&2
        exit 1
    fi

    log_step "Running mpv smoke checks"
    "${build_dir}/mpv" --version >"${logs_dir}/smoke.log" 2>&1
}

run_gstreamer() {
    local project_root="$1"
    local src_dir="$2"
    local logs_dir="$3"
    local build_dir="${project_root}/build"
    local python_venv_dir="${project_root}/python-venv"
    local meson_bin
    local ninja_bin
    local host_cxx
    local host_clang
    local host_clangxx
    local runner_tool_dir
    local runner_path
    local native_file

    meson_bin="$(find_tool meson)"
    ninja_bin="$(find_tool ninja)"
    host_cxx="$(find_host_cxx)"
    host_clang="$(find_host_clang)"
    host_clangxx="$(find_host_clangxx)"
    runner_tool_dir="${project_root}/runner-tools"
    populate_tool_dir \
        "${runner_tool_dir}" \
        meson \
        ninja \
        pkg-config \
        python3 \
        git \
        xcodebuild \
        bison \
        flex \
        glib-mkenums \
        glib-genmarshal \
        glib-compile-resources \
        glib-compile-schemas
    ln -sf "${host_clang}" "${runner_tool_dir}/clang"
    ln -sf "${host_clangxx}" "${runner_tool_dir}/clang++"
    runner_path="${runner_tool_dir}:/usr/bin:/bin:/usr/sbin:/sbin"
    native_file="${project_root}/gstreamer-native.ini"

    log_step "Preparing gstreamer Python environment"
    "${runner_tool_dir}/python3" -m venv "${python_venv_dir}" >"${logs_dir}/python-deps.log" 2>&1
    "${python_venv_dir}/bin/python3" -m pip install --disable-pip-version-check jinja2 >>"${logs_dir}/python-deps.log" 2>&1

    write_meson_native_file \
        "${native_file}" \
        "${toolchain_dir}/clang" \
        "${host_clangxx}" \
        "${host_clang}" \
        "${host_clangxx}" \
        "${runner_tool_dir}/pkg-config" \
        "${python_venv_dir}/bin/python3" \
        "${runner_tool_dir}/bison" \
        "${runner_tool_dir}/flex"

    log_step "Configuring gstreamer"
    PATH="${runner_path}" \
    CC="${toolchain_dir}/clang" \
    CXX="${host_cxx}" \
    OBJC="${host_clang}" \
    OBJCXX="${host_clangxx}" \
        "${meson_bin}" setup "${build_dir}" "${src_dir}" \
            --backend=ninja \
            --native-file "${native_file}" \
            --buildtype=debugoptimized \
            -Dbase=enabled \
            -Dgood=disabled \
            -Dugly=disabled \
            -Dbad=disabled \
            -Dlibav=disabled \
            -Ddevtools=disabled \
            -Dges=disabled \
            -Drtsp_server=disabled \
            -Drs=disabled \
            -Dgst-examples=disabled \
            -Dpython=disabled \
            -Dtls=disabled \
            -Dlibnice=disabled \
            -Dgtk=disabled \
            -Dgpl=disabled \
            -Dgst-full=disabled \
            -Dbuild-tools-source=system \
            -Dbenchmarks=disabled \
            -Dtools=enabled \
            -Dtests=disabled \
            -Dexamples=disabled \
            -Dintrospection=disabled \
            -Dnls=disabled \
            -Ddoc=disabled \
            -Dgtk_doc=disabled \
            -Dgst-plugins-base:gl=disabled \
            -Dgst-plugins-base:drm=disabled \
            -Dgst-plugins-base:x11=disabled \
            -Dgst-plugins-base:xshm=disabled \
            -Dgst-plugins-base:xvideo=disabled \
            -Dgst-plugins-base:xi=disabled \
            >"${logs_dir}/configure.log" 2>&1

    log_step "Building gstreamer"
    PATH="${runner_path}" \
    "${ninja_bin}" -C "${build_dir}" \
        subprojects/gstreamer/tools/gst-launch-1.0 \
        subprojects/gstreamer/tools/gst-inspect-1.0 \
        subprojects/gst-plugins-base/tools/gst-play-1.0 \
        >"${logs_dir}/build.log" 2>&1

    if [[ ! -x "${build_dir}/subprojects/gstreamer/tools/gst-launch-1.0" || \
          ! -x "${build_dir}/subprojects/gstreamer/tools/gst-inspect-1.0" || \
          ! -x "${build_dir}/subprojects/gst-plugins-base/tools/gst-play-1.0" ]]; then
        echo "gstreamer build did not produce the expected tool binaries" >&2
        exit 1
    fi

    log_step "Running gstreamer smoke checks"
    {
        file "${build_dir}/subprojects/gstreamer/tools/gst-launch-1.0"
        file "${build_dir}/subprojects/gstreamer/tools/gst-inspect-1.0"
        file "${build_dir}/subprojects/gst-plugins-base/tools/gst-play-1.0"
        otool -L "${build_dir}/subprojects/gstreamer/tools/gst-launch-1.0"
        otool -L "${build_dir}/subprojects/gstreamer/tools/gst-inspect-1.0"
        otool -L "${build_dir}/subprojects/gst-plugins-base/tools/gst-play-1.0"
    } >"${logs_dir}/smoke.log" 2>&1
}

run_ghostscript() {
    local src_dir="$1"
    local logs_dir="$2"
    local host_clang

    host_clang="$(find_host_clang)"

    log_step "Cleaning ghostscript tree"
    (
        cd "${src_dir}"
        make distclean >/dev/null 2>&1 || true
        rm -rf bin obj
        rm -f Makefile config.log config.status
    )

    log_step "Configuring ghostscript"
    (
        cd "${src_dir}"
        CC="${host_clang}" \
        CCAUX="${host_clang}" \
            ./configure \
                --without-x \
                --with-drivers="" \
                --without-pdf \
                --without-pcl \
                --without-xps \
                --without-tesseract \
                --disable-fontconfig \
                --disable-dbus \
                --disable-cups \
                --disable-gtk \
                --without-libidn \
                --without-libpaper \
                --without-pdftoraster \
                --without-ijs \
                >"${logs_dir}/configure.log" 2>&1
    )

    log_step "Building ghostscript"
    (
        cd "${src_dir}"
        make -j"${jobs}" \
            CC="${toolchain_dir}/clang" \
            CCAUX="${toolchain_dir}/clang" \
            >"${logs_dir}/build.log" 2>&1
    )

    if [[ ! -x "${src_dir}/bin/gs" ]]; then
        echo "ghostscript build did not produce bin/gs" >&2
        exit 1
    fi

    log_step "Running ghostscript smoke checks"
    (
        cd "${src_dir}"
        ./bin/gs -version >"${logs_dir}/smoke.log" 2>&1
    )
}

run_project() {
    local project="$1"
    local repo_url
    local repo_ref
    local project_root
    local src_dir
    local logs_dir

    repo_url="$(project_repo "${project}")"
    repo_ref="$(project_ref "${project}")"
    project_root="${validation_root}/${project}"
    src_dir="${project_root}/src"
    logs_dir="${project_root}/logs"

    rm -rf "${project_root}"
    mkdir -p "${logs_dir}"

    log_step "Fetching ${project} @ ${repo_ref}"
    populate_source_tree "${project}" "${repo_url}" "${repo_ref}" "${src_dir}" >"${logs_dir}/fetch.log" 2>&1

    case "${project}" in
        ffmpeg)
            run_ffmpeg "${src_dir}" "${logs_dir}"
            ;;
        librempeg)
            run_librempeg "${src_dir}" "${logs_dir}"
            ;;
        libplacebo)
            run_libplacebo "${project_root}" "${src_dir}" "${logs_dir}"
            ;;
        mpv)
            run_mpv "${project_root}" "${src_dir}" "${logs_dir}"
            ;;
        gstreamer)
            run_gstreamer "${project_root}" "${src_dir}" "${logs_dir}"
            ;;
        ghostscript)
            run_ghostscript "${src_dir}" "${logs_dir}"
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
