cmake_minimum_required(VERSION 3.15)
project(omtsched)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_library(omtsched SHARED omtsched.h
        Assignment.h Component.h ComponentType.h Condition.h
        Model.h Problem.h Rule.h Translator.h
        conditions/BasicConditions.h conditions/BooleanConditions.h conditions/OrderedConditions.h
        ../z3/TranslatorZ3.h
         "z3/ComponentConstraints.cpp")

set_target_properties(omtsched PROPERTIES LINKER_LANGUAGE CXX)

add_executable(examples
    ../examples/example.cpp "z3/ComponentConstraints.cpp")

target_link_libraries(examples omtsched)


## Z3

#find_package(Z3 CONFIG REQUIRED)
#target_include_directories(examples PRIVATE ${Z3_CXX_INCLUDE_DIRS})
#target_link_libraries(examples ${Z3_LIBRARIES})