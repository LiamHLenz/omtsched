//
// Created by hal on 12.11.21.
//


#include "../omtsched.h"
#include <initializer_list>
#include <fstream>

int main () {

    using namespace omtsched;

    Problem<std::string> simple;

    simple.addComponentType("Job");
    simple.addComponentType("Machine");
    simple.addComponentType("Timepoint");

