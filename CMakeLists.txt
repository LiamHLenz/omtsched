cmake_minimum_required(VERSION 3.15)
project(omtsched)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_library(omtsched SHARED omtsched.h
        Assignment.h Component.h ComponentType.h Condition.h
        Model.h Problem.h Rule.h Translator.h
        conditions/BasicConditions.h conditions/BooleanConditions.h conditions/OrderedConditions.h
        z3/TranslatorZ3.h
        )

set_target_properties(omtsched PROPERTIES LINKER_LANGUAGE CXX)
#target_compile_features(omtsched PRIVATE cxx_std_17)

message(proj: ${PROJECT_SOURCE_DIR})

add_executable(examples
    examples/example.cpp)

#target_link_libraries(examples omtsched)


################################################################################
#   Z3
################################################################################
list(APPEND CMAKE_PREFIX_PATH "${CMAKE_SOURCE_DIR}/../dependencies/z3")

message(PATH: ${CMAKE_PREFIX_PATH})

find_package(Z3
  REQUIRED
  CONFIG
)

message(STATUS "Z3_FOUND: ${Z3_FOUND}")
message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
message(STATUS "Z3_DIR: ${Z3_DIR}")

target_include_directories(examples PRIVATE ${Z3_CXX_INCLUDE_DIRS})

target_link_libraries(examples PRIVATE omtsched ${Z3_LIBRARIES})

target_compile_options(examples PRIVATE ${Z3_COMPONENT_CXX_FLAGS})

if (CMAKE_SYSTEM_NAME MATCHES "[Ww]indows")
  # On Windows we need to copy the Z3 libraries
  # into the same directory as the executable
  # so that they can be found.
  foreach (z3_lib ${Z3_LIBRARIES})
    message(STATUS "Adding copy rule for ${z3_lib}")
    add_custom_command(TARGET examples
      POST_BUILD
      COMMAND
        ${CMAKE_COMMAND} -E copy_if_different
        $<TARGET_FILE:${z3_lib}>
        $<TARGET_FILE_DIR:examples>
    )
  endforeach()
endif()
