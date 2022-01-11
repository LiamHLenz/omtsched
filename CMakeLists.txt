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


find_package(Boost REQUIRED)

find_package(Z3 CONFIG REQUIRED)

find_package(wxWidgets REQUIRED)
include(${wxWidgets_USE_FILE})

#if(Boost_FOUND)
    include_directories(${BOOST_INCLUDE_DIRS})

#    add_executable(examples
#            examples/example.cpp)

    add_executable(uitest
            ui/main.cpp ui/MainFrame.cpp ui/MainFrame.h
            ui/ComponentPanel.cpp ui/ComponentPanel.h
            ui/ComponentDialog.cpp ui/ComponentDialog.h ui/TypeDialog.cpp ui/TypeDialog.h ui/AssignmentPanel.cpp ui/AssignmentPanel.h ui/ModelPanel.cpp ui/ModelPanel.h)

    target_link_libraries(uitest ${wxWidgets_LIBRARIES})
    target_link_libraries(uitest omtsched)
    target_link_libraries(uitest Boost::boost)
    target_include_directories(uitest PRIVATE ${Z3_CXX_INCLUDE_DIRS})
    target_link_libraries(uitest ${Z3_LIBRARIES})

#    target_link_libraries(examples omtsched)
#    target_link_libraries(examples Boost::boost)
#    target_include_directories(examples PRIVATE ${Z3_CXX_INCLUDE_DIRS})
#    target_link_libraries(examples ${Z3_LIBRARIES})

#else()
#    message(FATAL_ERROR "boost libraries not found")
#endif()
