cmake_minimum_required(VERSION 3.15)
project(omtsched)

set(CMAKE_CXX_STANDARD 20)

add_library(omtsched SHARED omtsched.hpp omtsched.h components/Task.h components/Timeslot.h Problem.h
        Translator.h z3/TranslatorZ3.h z3/TranslatorZ3.hpp Model.h Rule.h Assignment.h Component.h Variable.h
        components/Agent.h components/Time.h components/TimedTask.h)
set_target_properties(omtsched PROPERTIES LINKER_LANGUAGE CXX)

# find_package(Boost REQUIRED COMPONENTS "date_time")

find_package(Z3 REQUIRED CONFIG)

#if(Boost_FOUND)
#    include_directories(${BOOST_INCLUDE_DIRS})

    add_executable(examples
            Condition.h examples/itc21.cpp ComponentType.h conditions/CompositeConditions.h conditions/BasicCondition.h)

#    target_link_libraries(examples ${Boost_DATE_TIME_LIBRARY} omtsched)
    target_include_directories(examples PRIVATE ${Z3_CXX_INCLUDE_DIRS})
    target_link_libraries(examples ${Z3_LIBRARIES})

#else()
#    message(FATAL_ERROR "boost libraries not found")
#endif()
