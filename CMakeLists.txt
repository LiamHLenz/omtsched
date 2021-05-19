cmake_minimum_required(VERSION 3.15)
project(omtsched)

set(CMAKE_CXX_STANDARD 20)

add_library(omtsched SHARED omtsched.hpp omtsched.h Task.h Timeslot.h Problem.hpp Problem.h Translator.h Translator.hpp Constraint.h)
set_target_properties(omtsched PROPERTIES LINKER_LANGUAGE CXX)

find_package(Boost REQUIRED COMPONENTS "date_time")

find_package(Z3 REQUIRED CONFIG)

if(Boost_FOUND)
    include_directories(${BOOST_INCLUDE_DIRS})

    add_executable(
            tester tester/testMain.cpp
            tester/semesterProblem.cpp Constraint.h)

    target_link_libraries(tester ${Boost_DATE_TIME_LIBRARY} omtsched)
    #target_include_directories(tester PRIVATE ${Z3_CXX_INCLUDE_DIRS})
    target_link_libraries(tester ${Z3_LIBRARIES})

else()
    message(FATAL_ERROR "boost libraries not found")
endif()
