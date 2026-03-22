if(NOT DEFINED ABURI)
    message(FATAL_ERROR "ABURI is required")
endif()

get_filename_component(REPO_ROOT "${CMAKE_CURRENT_LIST_DIR}/.." ABSOLUTE)
get_filename_component(ABURI_DIR "${ABURI}" DIRECTORY)

set(PUBLIC_TEST_DIR "${REPO_ROOT}/public_tests")
if(NOT IS_DIRECTORY "${PUBLIC_TEST_DIR}")
    message(FATAL_ERROR "public_tests directory is missing: ${PUBLIC_TEST_DIR}")
endif()

file(GLOB PUBLIC_TEST_SOURCES LIST_DIRECTORIES false
    "${PUBLIC_TEST_DIR}/*.c"
    "${PUBLIC_TEST_DIR}/*.cc"
    "${PUBLIC_TEST_DIR}/*.cpp"
    "${PUBLIC_TEST_DIR}/*.cxx"
    "${PUBLIC_TEST_DIR}/*.c++"
    "${PUBLIC_TEST_DIR}/*.cp"
    "${PUBLIC_TEST_DIR}/*.C")
list(SORT PUBLIC_TEST_SOURCES)

if(PUBLIC_TEST_SOURCES STREQUAL "")
    message(FATAL_ERROR "No public test sources found in ${PUBLIC_TEST_DIR}")
endif()

set(WORK_DIR "${ABURI_DIR}/public-tests-check")
file(REMOVE_RECURSE "${WORK_DIR}")
file(MAKE_DIRECTORY "${WORK_DIR}")

set(EXPECTED_EXIT_CODE 67)
set(FAILED_TESTS "")

foreach(SRC IN LISTS PUBLIC_TEST_SOURCES)
    get_filename_component(TEST_FILE_NAME "${SRC}" NAME)
    get_filename_component(TEST_EXT "${SRC}" EXT)
    string(REPLACE "." "_" TEST_NAME "${TEST_FILE_NAME}")
    set(BIN "${WORK_DIR}/${TEST_NAME}")
    set(COMPILE_ARGS "${SRC}" -o "${BIN}")

    if(TEST_EXT STREQUAL ".C")
        set(COMPILE_ARGS -x c++ "${SRC}" -o "${BIN}")
    else()
        string(TOLOWER "${TEST_EXT}" TEST_EXT_LOWER)
        if(TEST_EXT_LOWER STREQUAL ".cc" OR
                TEST_EXT_LOWER STREQUAL ".cpp" OR
                TEST_EXT_LOWER STREQUAL ".cxx" OR
                TEST_EXT_LOWER STREQUAL ".c++" OR
                TEST_EXT_LOWER STREQUAL ".cp")
            set(COMPILE_ARGS -x c++ "${SRC}" -o "${BIN}")
        endif()
    endif()

    execute_process(
        COMMAND "${ABURI}" ${COMPILE_ARGS}
        RESULT_VARIABLE COMPILE_RES
        OUTPUT_VARIABLE COMPILE_OUT
        ERROR_VARIABLE COMPILE_ERR
    )

    if(NOT COMPILE_RES EQUAL 0)
        string(APPEND FAILED_TESTS
            "\n[compile] ${TEST_NAME}\n"
            "stdout:\n${COMPILE_OUT}\n"
            "stderr:\n${COMPILE_ERR}\n")
        continue()
    endif()

    if(NOT EXISTS "${BIN}")
        string(APPEND FAILED_TESTS
            "\n[missing-binary] ${TEST_NAME}\n"
            "compiler reported success but did not produce ${BIN}\n")
        continue()
    endif()

    execute_process(
        COMMAND "${BIN}"
        RESULT_VARIABLE RUN_RES
        OUTPUT_VARIABLE RUN_OUT
        ERROR_VARIABLE RUN_ERR
    )

    if(NOT RUN_RES EQUAL ${EXPECTED_EXIT_CODE})
        string(APPEND FAILED_TESTS
            "\n[run] ${TEST_NAME}\n"
            "expected exit code: ${EXPECTED_EXIT_CODE}\n"
            "actual exit code: ${RUN_RES}\n"
            "stdout:\n${RUN_OUT}\n"
            "stderr:\n${RUN_ERR}\n")
    endif()
endforeach()

if(NOT FAILED_TESTS STREQUAL "")
    message(FATAL_ERROR "public_tests check failed:${FAILED_TESTS}")
endif()
