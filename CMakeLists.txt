cmake_minimum_required(VERSION 3.15)
project(omtsched)

set(CMAKE_CXX_STANDARD 20)

add_library(omtsched SHARED omtsched.hpp omtsched.h Task.h Timeslot.h Problem.hpp Problem.h Translator.h Translator.hpp)
set_target_properties(omtsched PROPERTIES LINKER_LANGUAGE CXX)

find_package(Boost REQUIRED COMPONENTS "date_time")

if(Boost_FOUND)
    include_directories(${BOOST_INCLUDE_DIRS})

    add_executable(
            tester tester/testMain.cpp
    )

    target_link_libraries(tester ${Boost_DATE_TIME_LIBRARY} omtsched)

else()
    message(FATAL_ERROR "boost libraries not found")
endif()
