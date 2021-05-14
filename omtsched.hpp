#include <iostream>
#include <utility>
#include <z3.h>
#include <z3++.h>

void hello() {
    std::cout << "Hello, World!" << std::endl;
}




template <typename TimeslotID, typename TaskID>
std::string assignID(const TimeslotID &tsid, const TaskID &aid){

    return "assign_" + tsid + "_" + aid;

}

