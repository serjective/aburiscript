cmake_minimum_required(VERSION 4.1)
project(aburi)

set(ABURI_SUPPORTED_LLVM_MIN_VERSION 18.0.0)
set(ABURI_SUPPORTED_LLVM_MAX_VERSION 19.0.0)
option(ABURI_BUILD_PUBLIC_TESTS "Build Aburiscript public runtime smoke tests" OFF)
option(ABURI_BUILD_TESTS "Build Aburiscript private test suite" OFF)

find_package(LLVM REQUIRED CONFIG)

if(LLVM_PACKAGE_VERSION VERSION_LESS ${ABURI_SUPPORTED_LLVM_MIN_VERSION}
        OR LLVM_PACKAGE_VERSION VERSION_GREATER_EQUAL ${ABURI_SUPPORTED_LLVM_MAX_VERSION})
        message(FATAL_ERROR
                "Aburiscript currently supports LLVM 18.x only. "
                "Found LLVM ${LLVM_PACKAGE_VERSION} at ${LLVM_DIR}. "
                "Point CMake at an LLVM 18 installation with "
                "-DLLVM_DIR=<path-to-llvm-18>/lib/cmake/llvm or "
                "-DCMAKE_PREFIX_PATH=<path-to-llvm-prefix>.")
endif()

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

set(CMAKE_CXX_STANDARD 20)

set(COLLECT_SOURCES
        collect/decl_context.cpp
        collect/lookup_engine.cpp
        collect/collect_core.cpp
        collect/collect_convert.cpp
        collect/collect_convert_arith.cpp
        collect/collect_convert_pointer.cpp
        collect/collect_convert_diag.cpp
        collect/collect_expr.cpp
        collect/collect_overload.cpp
        collect/collect_calls.cpp
        collect/collect_member_access.cpp
        collect/collect_stmt.cpp
        collect/collect_decl.cpp
        collect/collect_decl_variable.cpp
        collect/collect_decl_variable_helpers.cpp
        collect/collect_decl_symbols.cpp
        collect/query_context.cpp
        collect/collect_record.cpp
        collect/collect_init.cpp
        collect/collect_templates_arguments.cpp
        collect/collect_templates_packs.cpp
        collect/collect_templates_records.cpp
        collect/collect_templates_clone.cpp
        collect/collect_templates_deduction.cpp
        collect/collect_templates_deferred.cpp
        collect/collect_templates_function_specialization.cpp
        collect/collect_templates_variable_specialization.cpp
        collect/collect_templates_class_specialization.cpp
        collect/collect_templates_substitution.cpp
        collect/collect_templates_materialize.cpp
        collect/collect_templates_finalize.cpp
        collect/collect_type.cpp
)

set(CONSTEVAL_SOURCES
        constexpr/consteval_engine.cpp
        constexpr/consteval_engine.h
        constexpr/consteval_compat.cpp
        constexpr/consteval_compat.h
        constexpr/pp_consteval.cpp
        constexpr/pp_consteval.h
        constexpr/consteval_diag.h
        constexpr/consteval_mode.h
        constexpr/consteval_result.h
        constexpr/const_value.cpp
        constexpr/const_value.h
        constexpr/eval_memory.cpp
        constexpr/eval_memory.h
        constexpr/eval_state.cpp
        constexpr/eval_state.h
)

set(ABI_SOURCES
        abi/abi_policy.cpp
        abi/abi_policy.h
        abi/darwin_blocks.cpp
        abi/darwin_blocks.h
        abi/mangle.cpp
        abi/mangle.h
)

set(PARSER_SOURCES
        parser/parser.cpp
        parser/parser_tentative.cpp
        parser/parser_expr.cpp
        parser/parser_decl.cpp
        parser/parser_record.cpp
        parser/parser_record_deferred.cpp
        parser/parser_cxx_qualified.cpp
        parser/parser_cxx_out_of_line.cpp
        parser/parser_declarator.cpp
        parser/parser_stmt.cpp
        parser/parser_cxx.cpp
        parser/parser.h
)

set(SHARED_HELPER_SOURCES
        helpers/casting.h
        helpers/auto_type_utils.cpp
        helpers/auto_type_utils.h
        helpers/qualified_name_utils.cpp
        helpers/qualified_name_utils.h
)

set(ABURI_LIBRARY_SOURCES
        libaburi/library.cpp
        lexer.cpp
        lexer.h
        ${PARSER_SOURCES}
        ${SHARED_HELPER_SOURCES}
        ast/ast.h
        ast/ast.cpp
        ast/ast_clone.cpp
        ast/ast_clone.h
        ast/expr_clone.cpp
        ast/expr_clone.h
        ast/ast_context.cpp
        ast/ast_context.h
        ast/semantic_store.cpp
        ast/semantic_store.h
        ast/ast_memory_report.cpp
        ast/ast_memory_report.h
        ast/attributes.cpp
        ast/attributes.h
        ast/symbols.cpp
        ast/symbols.h
        ast/types.cpp
        ast/types.h
        ast/special_members.cpp
        ast/special_members.h
        abi/target_info.cpp
        abi/target_info.h
        abi/bitfield_layout.cpp
        abi/bitfield_layout.h
        ast2llvm/ast2llvm.cpp
        ast2llvm/ast2llvm.h
        ast2llvm/const_lowering.cpp
        ast2llvm/const_lowering.h
        ast2llvm/arith.cpp
        ast2llvm/flow.cpp
        ast2llvm/lower_ops.cpp
        ast2llvm/lower_vars.cpp
        ast2llvm/lower_cast.cpp
        ast2llvm/lower_cpp_subobject.cpp
        ast2llvm/lower_init_list.cpp
        ast2llvm/lower_object_access.cpp
        ast2llvm/lower_control_flow.cpp
        ast2llvm/lower_eh_expr.cpp
        ast2llvm/lower_calls.cpp
        ast2llvm/lower_asm.cpp
        ast2llvm/lower_rtti.cpp
        libaburi/library.h
        source_mgnt.cpp
        source_mgnt.h
        preprocessor.cpp
        preprocessor.h
        builtin_registry.cpp
        builtin_registry.h
        toolchain_profile.cpp
        toolchain_profile.h
        numeric_utils.h
        diagnostics.cpp
        diagnostics.h
        ${ABI_SOURCES}
        ${CONSTEVAL_SOURCES}
        ${COLLECT_SOURCES}
        ast2llvm/builtin.cpp
        ast2llvm/lower_ctor_dtor.cpp
        ast2llvm/lower_vtable.cpp
)

add_library(aburi_lib STATIC ${ABURI_LIBRARY_SOURCES})
target_include_directories(aburi_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

add_executable(aburi main.cpp)

llvm_map_components_to_libnames(llvm_libs support core irreader executionengine orcjit native scalaropts transformutils ipo analysis passes)

target_link_libraries(aburi_lib PUBLIC ${llvm_libs})
target_link_libraries(aburi PRIVATE aburi_lib)

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

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/tests/CMakeLists.txt")
        if(ABURI_BUILD_TESTS)
                add_subdirectory(tests cmake-tests)
        endif()
elseif(ABURI_BUILD_TESTS)
        message(FATAL_ERROR
                "ABURI_BUILD_TESTS=ON, but ${CMAKE_CURRENT_SOURCE_DIR}/tests/CMakeLists.txt "
                "is missing.")
endif()
