
cmake_minimum_required(VERSION 3.11.4)
project (impcheck_modules)
enable_language(ASM)

add_definitions("-std=gnu99 -Wall -Wextra -flto -g")
if(IMPCHECK_WRITE_DIRECTIVES)
    add_definitions("-DIMPCHECK_WRITE_DIRECTIVES=${IMPCHECK_WRITE_DIRECTIVES}")
endif()
if(IMPCHECK_FLUSH_ALWAYS)
    add_definitions("-DIMPCHECK_FLUSH_ALWAYS=${IMPCHECK_FLUSH_ALWAYS}")
endif()
if(IMPCHECK_OVERRIDE_SALT)
    file(WRITE src/trusted/salt.h "#define IMPCHECK_SALT " ${IMPCHECK_OVERRIDE_SALT})
else()
    execute_process(COMMAND bash "-c" "dd if=/dev/urandom count=8 bs=1 2>/dev/null | od -t u8 | awk '{print $2\"UL\"}' | head -1" OUTPUT_VARIABLE IMPCHECK_SALT)
    file(WRITE src/trusted/salt.h "#define IMPCHECK_SALT " ${IMPCHECK_SALT})
endif()

add_executable(impcheck_parse
    src/trusted/hash.c src/trusted/secret.c src/trusted/siphash.c src/trusted/trusted_parser.c src/trusted/trusted_utils.c src/trusted/vectors.c src/writer.c 
    src/trusted/main_parse.c)
#add_custom_command(
#    OUTPUT ${CMAKE_CURRENT_SOURCE_DIR}/src/trusted/cakeml/rup.S
#    COMMAND ./cake --main_return=true < rup.cml > rup.S
#    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/src/trusted/cakeml/rup.cml
#    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/src/trusted/cakeml
#    COMMENT "Building rup.S from rup.cml"
#)
#add_custom_target(rup_cml ALL DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/src/trusted/cakeml/rup.S)

# This is the important one for verified checking 
add_executable(impcheck_check
    src/trusted/confirm.c src/trusted/hash.c src/trusted/secret.c src/trusted/siphash.c
    src/trusted/trusted_checker.c src/trusted/trusted_utils.c src/trusted/vectors.c src/writer.c
    src/trusted/cakeml/cake_distrup.S
    src/trusted/main_check.c)

add_executable(impcheck_confirm
    src/trusted/confirm.c src/trusted/hash.c src/trusted/secret.c src/trusted/siphash.c src/trusted/trusted_parser.c src/trusted/trusted_utils.c src/trusted/vectors.c src/writer.c 
    src/trusted/main_confirm.c)

add_executable(test_hash src/trusted/trusted_utils.c src/trusted/hash.c src/writer.c test/test.c
    test/test_hash.c)
add_executable(test_full src/trusted/trusted_utils.c src/writer.c test/test.c src/trusted/vectors.c
    test/test_full.c)
