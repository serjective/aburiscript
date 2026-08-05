cmake_minimum_required(VERSION 3.24)

set(ADINKRA_VERSION 0.1.0)

if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
    project(adinkra
        VERSION ${ADINKRA_VERSION}
        DESCRIPTION "Adinkra C++ standard library"
        LANGUAGES C CXX)
    set(ADINKRA_STANDALONE ON)
else()
    set(ADINKRA_STANDALONE OFF)
endif()

# A standalone Adinkra build with another compiler is a user error worth
# failing on. Inside the Aburi superbuild the root project has already checked
# this and skipped the subdirectory, so reaching here means Clang.
if(ADINKRA_STANDALONE AND NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    message(FATAL_ERROR "Adinkra is currently developed and tested with Clang")
endif()

option(ADINKRA_BUILD_TESTS "Build the Clang-first Adinkra test suite"
    ${ADINKRA_STANDALONE})
option(ADINKRA_BUILD_SHARED
    "Build a shared Adinkra runtime for programs that load C++ modules"
    ON)
option(ADINKRA_ENABLE_SANITIZERS "Enable AddressSanitizer and UndefinedBehaviorSanitizer" OFF)

set(ADINKRA_INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/include/c++/v1")

add_library(adinkra_compile_options INTERFACE)
target_compile_features(adinkra_compile_options INTERFACE cxx_std_20)
target_compile_options(adinkra_compile_options INTERFACE
    $<$<COMPILE_LANGUAGE:CXX>:-nostdinc++>)
target_link_options(adinkra_compile_options INTERFACE
    $<$<LINK_LANGUAGE:CXX>:-nostdlib++>)
if(APPLE)
    target_link_libraries(adinkra_compile_options INTERFACE c++abi)
endif()
target_include_directories(adinkra_compile_options SYSTEM INTERFACE
    "$<BUILD_INTERFACE:${ADINKRA_INCLUDE_DIR}>"
    "$<INSTALL_INTERFACE:include/adinkra/c++/v1>")

set(ADINKRA_RUNTIME_SOURCES
    runtime/atomic.cpp
    runtime/exception.cpp
    runtime/fstream.cpp
    runtime/io.cpp
    runtime/locale.cpp
    runtime/new.cpp
    runtime/regex.cpp
    runtime/storage.cpp
    runtime/stdexcept.cpp
    runtime/string.cpp
    runtime/sstream.cpp
    runtime/system_error.cpp
    runtime/tree.cpp
    runtime/variant.cpp)

add_library(adinkra STATIC ${ADINKRA_RUNTIME_SOURCES})
add_library(adinkra::adinkra ALIAS adinkra)
target_link_libraries(adinkra PUBLIC adinkra_compile_options)
target_compile_options(adinkra PRIVATE
    -Wall
    -Wextra
    -Wpedantic)
set_target_properties(adinkra PROPERTIES
    OUTPUT_NAME adinkra
    CXX_EXTENSIONS OFF
    POSITION_INDEPENDENT_CODE ON)

if(ADINKRA_BUILD_SHARED)
    add_library(adinkra_shared SHARED ${ADINKRA_RUNTIME_SOURCES})
    add_library(adinkra::adinkra_shared ALIAS adinkra_shared)
    target_link_libraries(adinkra_shared PUBLIC adinkra_compile_options)
    target_compile_options(adinkra_shared PRIVATE
        -Wall
        -Wextra
        -Wpedantic)
    set_target_properties(adinkra_shared PROPERTIES
        OUTPUT_NAME adinkra
        CXX_EXTENSIONS OFF
        POSITION_INDEPENDENT_CODE ON
        VERSION "${ADINKRA_VERSION}"
        SOVERSION "0")
endif()

if(ADINKRA_ENABLE_SANITIZERS)
    target_compile_options(adinkra PRIVATE -fsanitize=address,undefined -fno-omit-frame-pointer)
    target_link_options(adinkra PUBLIC -fsanitize=address,undefined)
    if(ADINKRA_BUILD_SHARED)
        target_compile_options(adinkra_shared PRIVATE
            -fsanitize=address,undefined
            -fno-omit-frame-pointer)
        target_link_options(adinkra_shared PUBLIC
            -fsanitize=address,undefined)
    endif()
endif()

include(GNUInstallDirs)
include(CMakePackageConfigHelpers)
configure_package_config_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/adinkraConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/adinkraConfig.cmake"
    INSTALL_DESTINATION "${CMAKE_INSTALL_LIBDIR}/cmake/adinkra")
write_basic_package_version_file(
    "${CMAKE_CURRENT_BINARY_DIR}/adinkraConfigVersion.cmake"
    VERSION "${ADINKRA_VERSION}"
    COMPATIBILITY SameMajorVersion)
install(TARGETS adinkra adinkra_compile_options
    EXPORT adinkraTargets
    ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}")
if(ADINKRA_BUILD_SHARED)
    install(TARGETS adinkra_shared
        EXPORT adinkraTargets
        LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
        RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}")
endif()
install(DIRECTORY "${ADINKRA_INCLUDE_DIR}/"
    DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/adinkra/c++/v1")
install(EXPORT adinkraTargets
    FILE adinkraTargets.cmake
    NAMESPACE adinkra::
    DESTINATION "${CMAKE_INSTALL_LIBDIR}/cmake/adinkra")
install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/adinkraConfig.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/adinkraConfigVersion.cmake"
    DESTINATION "${CMAKE_INSTALL_LIBDIR}/cmake/adinkra")

if(ADINKRA_BUILD_TESTS)
    include(CTest)
    enable_testing()
    add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/../tests/adinkra"
        "${CMAKE_CURRENT_BINARY_DIR}/tests")
endif()
