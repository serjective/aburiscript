cmake_minimum_required(VERSION 4.1)
project(aburi)

set(ABURI_SUPPORTED_LLVM_MIN_VERSION 22.0.0)
set(ABURI_SUPPORTED_LLVM_MAX_VERSION 23.0.0)
option(ABURI_BUILD_PUBLIC_TESTS "Build Aburi public runtime smoke tests" OFF)
option(ABURI_BUILD_TESTS "Build Aburi private test suite" OFF)
option(ABURI_BUILD_ADINKRA "Build the standalone Adinkra library" ON)

find_package(LLVM REQUIRED CONFIG)

if(LLVM_PACKAGE_VERSION VERSION_LESS ${ABURI_SUPPORTED_LLVM_MIN_VERSION}
        OR LLVM_PACKAGE_VERSION VERSION_GREATER_EQUAL ${ABURI_SUPPORTED_LLVM_MAX_VERSION})
    message(FATAL_ERROR
        "Aburi currently supports LLVM 22.x only. "
        "Found LLVM ${LLVM_PACKAGE_VERSION} at ${LLVM_DIR}. "
        "Point CMake at an LLVM 22 installation with "
        "-DLLVM_DIR=<path-to-llvm-22>/lib/cmake/llvm or "
        "-DCMAKE_PREFIX_PATH=<path-to-llvm-prefix>.")
endif()

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
add_definitions(${LLVM_DEFINITIONS})

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(ABURI_FRONTEND_SOURCES
    libaburi/library.cpp
    libaburi/modules/scan.cpp
    libaburi/modules/session.cpp
    libaburi/serialize/bmi.cpp
    libaburi/serialize/compat.cpp
    lexer.cpp
    source_mgnt.cpp
    diagnostics.cpp
    attributes.cpp
    builtin_registry.cpp
    perf_stats.cpp
    toolchain_profile.cpp
    preprocessor.cpp
    constexpr/const_value.cpp
    constexpr/constant_state.cpp
    constexpr/eval_memory.cpp
    constexpr/eval_state.cpp
    constexpr/consteval_engine.cpp
    constexpr/metafn_eval.cpp
    constexpr/pp_consteval.cpp
    abi/target_info.cpp
    abi/abi_policy.cpp
    abi/aarch64_call_classify.cpp
    abi/x86_64_call_classify.cpp
    abi/call_classify.cpp
    abi/ilp32_classify_common.cpp
    abi/or1k_call_classify.cpp
    abi/darwin_blocks.cpp
    abi/objc_runtime.cpp
    parser/syntax_tree.cpp
    cir/builder.cpp
    cirpasses/coro_split.cpp
    cirpasses/objc_lower.cpp
    cir/examples.cpp
    cir/file.cpp
    cir/file_serialize.cpp
    cir/module_import.cpp
    cir/inst_schema.cpp
    cir/layout.cpp
    cir/type.cpp
    abi/mangle_cir.cpp
)

set(ABURI_NUMERIC_SOURCES
    numeric/floating_point.cpp
    numeric/floating_cir.cpp
)

set(ABURI_LLVM_SOURCES
    libaburi/jit.cpp
    cir2llvm/cir2llvm.cpp
    cir2llvm/lower_abi.cpp
    cir2llvm/lower_check.cpp
    cir2llvm/lower_entities.cpp
    cir2llvm/lower_insts.cpp
    cir2llvm/lower_types.cpp
    cir2llvm/lowerer.cpp
    cir2llvm/target_support.cpp
)


set(ABURI_COLLECT_SOURCES
    libaburi/frontend.cpp
    collect/collect.cpp
    collect/collect_attributes.cpp
    collect/collect_blocks.cpp
    collect/collect_convert.cpp
    collect/collect_coroutine.cpp
    collect/collect_module.cpp
    collect/collect_module_serialize.cpp
    collect/collect_module_templates.cpp
    collect/collect_lambda.cpp
    collect/collect_objc.cpp
    collect/collect_objc_arc.cpp
    collect/collect_core.cpp
    collect/collect_type_traits.cpp
    collect/collect_decl.cpp
    collect/collect_eh.cpp
    collect/collect_expr.cpp
    collect/collect_init.cpp
    collect/collect_lookup.cpp
    collect/collect_overload.cpp
    collect/collect_compare.cpp
    collect/collect_template.cpp
    collect/collect_template_clone.cpp
    collect/collect_template_deduce.cpp
    collect/collect_template_order.cpp
    collect/collect_record.cpp
    collect/collect_stmt.cpp
    collect/collect_structured_binding.cpp
    collect/collect_type.cpp
)
set(ABURI_PARSER_SOURCES
    parser/parser.cpp
    parser/parser_decl.cpp
    parser/parser_declarator.cpp
    parser/parser_stmt.cpp
    parser/parser_expr.cpp
    parser/parser_module.cpp
    parser/parser_objc.cpp
    parser/parser_pack.cpp
    parser/parser_record.cpp
    parser/parser_record_deferred.cpp
    parser/parser_tentative.cpp
    parser/parser_cxx.cpp
    parser/parser_cxx_qualified.cpp
    parser/parser_cxx_out_of_line.cpp
)


set(ABURI_AIR_SOURCES
    air/builder.cpp
    air/dominators.cpp
    air/function.cpp
    air/insts.cpp
    air/legalize.cpp
    air/legalize_i64.cpp
    air/legalize_soft_float.cpp
    air/module.cpp
    air/parse.cpp
    air/passes.cpp
    air/passes_opt.cpp
    air/print.cpp
    air/types.cpp
    air/verifier.cpp
    cir2air/lower_call.cpp
    cir2air/lower_insts.cpp
    cir2air/lowerer.cpp
    backend/backend.cpp
    backend/common/elf.cpp
    backend/common/macho.cpp
    backend/common/eh_metadata.cpp
    backend/common/mir_verifier.cpp
    backend/common/regalloc_fast.cpp
    backend/common/regalloc_linear.cpp
    backend/aarch64/insts.cpp
    backend/aarch64/isa.cpp
    backend/aarch64/isel.cpp
    backend/aarch64/frame.cpp
    backend/aarch64/asm_emit.cpp
    backend/aarch64/encode.cpp
    backend/aarch64/elf_emit.cpp
    backend/aarch64/elf_unwind.cpp
    backend/aarch64/macho_emit.cpp
    backend/x86/insts.cpp
    backend/x86/isa.cpp
    backend/x86/isel.cpp
    backend/x86/frame.cpp
    backend/x86/asm_emit.cpp
    backend/x86/encode.cpp
    backend/x86/macho_emit.cpp
    backend/x86/elf_emit.cpp
    backend/or1k/insts.cpp
    backend/or1k/isel.cpp
    backend/or1k/frame.cpp
    backend/or1k/asm_emit.cpp
)
add_library(aburi_air_lib OBJECT ${ABURI_AIR_SOURCES})
target_include_directories(aburi_air_lib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})


set(ABURI_ASSEMBLER_SOURCES
    assembler/aarch64/asm_aarch64.cpp
    assembler/x86/asm_x86.cpp
    assembler/assembler.cpp
    assembler/directives.cpp
    assembler/expr.cpp
    assembler/fragment.cpp
    assembler/lexer.cpp
    assembler/sink_macho.cpp
    assembler/symbols.cpp
)
add_library(aburi_assembler_lib OBJECT ${ABURI_ASSEMBLER_SOURCES})
target_include_directories(aburi_assembler_lib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

add_library(aburi_numeric_lib OBJECT ${ABURI_NUMERIC_SOURCES})
target_include_directories(aburi_numeric_lib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

add_library(aburi_collect_lib OBJECT ${ABURI_COLLECT_SOURCES})
target_include_directories(aburi_collect_lib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_precompile_headers(aburi_collect_lib PRIVATE collect/collect.h)

add_library(aburi_parser_lib OBJECT ${ABURI_PARSER_SOURCES})
target_include_directories(aburi_parser_lib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_precompile_headers(aburi_parser_lib PRIVATE parser/parser.h)


set(ABURI_GENERATED_DIR "${CMAKE_CURRENT_BINARY_DIR}/generated")
file(MAKE_DIRECTORY "${ABURI_GENERATED_DIR}")
set(ABURI_ARM_NEON_SRC "${CMAKE_CURRENT_SOURCE_DIR}/builtin_headers/arm_neon.h")
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS "${ABURI_ARM_NEON_SRC}")
file(READ "${ABURI_ARM_NEON_SRC}" ABURI_ARM_NEON_CONTENT)
file(WRITE "${ABURI_GENERATED_DIR}/aburi_arm_neon_h.inc"
    "// Generated from builtin_headers/arm_neon.h -- do not edit.\nR\"ABURI_NEON_EMBED(\n${ABURI_ARM_NEON_CONTENT})ABURI_NEON_EMBED\"\n")

add_library(aburi_frontend_core_lib OBJECT ${ABURI_FRONTEND_SOURCES})
target_include_directories(aburi_frontend_core_lib PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${ABURI_GENERATED_DIR})

add_library(aburi_llvm_lib OBJECT ${ABURI_LLVM_SOURCES})
target_include_directories(aburi_llvm_lib PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${LLVM_INCLUDE_DIRS})

add_library(aburi_lib STATIC
    $<TARGET_OBJECTS:aburi_frontend_core_lib>
    $<TARGET_OBJECTS:aburi_numeric_lib>
    $<TARGET_OBJECTS:aburi_air_lib>
    $<TARGET_OBJECTS:aburi_assembler_lib>
    $<TARGET_OBJECTS:aburi_collect_lib>
    $<TARGET_OBJECTS:aburi_parser_lib>
    $<TARGET_OBJECTS:aburi_llvm_lib>)
target_include_directories(aburi_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR} ${ABURI_GENERATED_DIR} ${LLVM_INCLUDE_DIRS})
llvm_map_components_to_libnames(llvm_libs
    support
    core
    target
    mc
    asmprinter
    codegen
    executionengine
    orcjit
    native
    passes
    AArch64
)
target_link_libraries(aburi_lib PUBLIC ${llvm_libs})

add_executable(aburi main.cpp driver/options.cpp)
target_link_libraries(aburi PRIVATE aburi_lib)

if(ABURI_BUILD_ADINKRA AND NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    message(WARNING
        "Adinkra requires Clang; disabling it for this ${CMAKE_CXX_COMPILER_ID} "
        "build. C++ then falls back to libstdc++, which is not yet usable with "
        "Aburi (see docs/stdlib_compatibility.md), so the resulting compiler has "
        "no working hosted C++. Configure with a Clang CMAKE_CXX_COMPILER to get "
        "Adinkra.")
    set(ABURI_BUILD_ADINKRA OFF)
endif()

if(ABURI_BUILD_ADINKRA)
    add_subdirectory(adinkra)
endif()

# The compiler's default C++ standard library has to exist on disk beside it, so
# a targeted "--build --target aburi" produces a usable toolchain rather than
# one whose headers are missing. This is a build-order edge only: aburi itself
# is a C++ program built by the host compiler and never links Adinkra.
if(TARGET adinkra)
    add_dependencies(aburi adinkra)
    if(TARGET adinkra_shared)
        add_dependencies(aburi adinkra_shared)
    endif()
endif()

# The driver resolves its resources relative to its own location, so an install
# has to place the builtin headers where that probe looks.
include(GNUInstallDirs)
install(TARGETS aburi RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}")
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/builtin_headers/"
    DESTINATION "${CMAKE_INSTALL_LIBDIR}/aburi/builtin_headers"
    PATTERN ".DS_Store" EXCLUDE)

if(ABURI_BUILD_PUBLIC_TESTS OR ABURI_BUILD_TESTS)
    include(CTest)
    enable_testing()
endif()

if(ABURI_BUILD_PUBLIC_TESTS)
    add_test(
        NAME public_tests_runtime
        COMMAND ${CMAKE_COMMAND}
        -DABURI=$<TARGET_FILE:aburi>
        -P ${PROJECT_SOURCE_DIR}/cmake/check_public_tests.cmake
    )
endif()

if(ABURI_BUILD_TESTS)
    add_subdirectory(tests ${PROJECT_BINARY_DIR}/tests-build)
endif()
