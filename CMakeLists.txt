cmake_minimum_required(VERSION 3.15)
project(omtsched)

set(CMAKE_CXX_STANDARD 20)

find_package(Boost REQUIRED COMPONENTS date_time)

add_library(omtsched SHARED omtsched.cpp omtsched.h Task.cpp Task.h Timeslot.cpp Timeslot.h)

add_executable(tester tester/testMain.cpp)

target_link_libraries(tester omtsched)