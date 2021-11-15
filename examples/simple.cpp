//
// Created by hal on 11.11.21.
//

#include "../omtsched.h"
#include <initializer_list>


int main () {

    omtsched::Problem<std::string> simple;

    simple.addComponentType("Player");
    simple.addComponentType("Court");
    simple.addComponentType("Time");

    for(const std::string &name : {"Anna", "Daniel", "Maria"}) {
        auto &player = simple.newComponent(name, "Player");
        player.addGroup("Early");
    }

    for(const std::string &name : {"Andre", "Eva", "Peter"}) {
        auto &player = simple.newComponent(name, "Player");
        player.addGroup("Late");
    }

    for(const int day : {1, 2, 3}) {
        auto &early = simple.newComponent("Day" + std::to_string(day) + "Early", "Time");
        early.addGroup("Early");

        auto &late = simple.newComponent("Day" + std::to_string(day) + "Late", "Time");
        late.addGroup("Late");
    }

    simple.newComponent("C1", "Court");
    simple.newComponent("C2", "Court");

    auto &game1 = simple.newAssignment("Game1");
    auto &game2 = simple.newAssignment("Game2");

    auto &game3 = simple.newAssignment("Game3");
    auto &game4 = simple.newAssignment("Game4");

    auto &game5 = simple.newAssignment("Game5");
    auto &game6 = simple.newAssignment("Game6");


    // Two Games simultaneous (same day + same group):
    // 1. Distinct Courts
    // 2. Distinct Players
    auto simultaneous = ;
    simple.addRule(implies(simultaneous, distinct("Player")))

    // If both players prefer late games, do not assign an early slot
    // and vice versa

}