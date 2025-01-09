//
// Created by hal on 05.11.21.
//

#include "../src/omtsched.h"
#include "../src/conditions/OrderedConditions.h"
#include <initializer_list>
#include <fstream>

enum ZebraComponents { COLOUR = "Colour", NATIONALITY = "Nation", DRINK = "Drink", SMOKE = "Smoke", PET = "Pet", POSITION = "Position" };

void getZebra(omtsched::Problem<std::string> &simple) {

    using namespace omtsched;
    using ZebraComponents;

    for (std::string str: {"Yellow", "Blue", "Red", "Ivory", "Green"})
        simple.newComponent(str, COLOUR);

    for (std::string str: {"English", "Spanish", "Norwegian", "Ukrainian", "Japanese"})
        simple.newComponent(str, NATIONALITY);

    for (std::string str: {"Water", "Tea", "Milk", "Orange Juice", "Coffee"})
        simple.newComponent(str, DRINK);

    for (std::string str: {"Kools", "Chesterfields", "Lucky Strike", "Parliaments", "Old Gold"})
        simple.newComponent(str, SMOKE);

    for (std::string str: {"Zebra", "Fox", "Horse", "Snails", "Dog"})
        simple.newComponent(str, PET);

    for (std::string str : {"1", "2", "3", "4", "5"})
        simple.newOrderedComponent(str, positionT, std::stoi(str));

    simple.addRule(uniqueComponents(true)); // implicit

    Assignment house;
    house.addComponent([POSITION, COLOUR, NATIONALITY, DRINK, SMOKE, PET]);

    simple.createAssignments(house, 5);
    simple.addRule(distinct<>(house, POSITION));

    //
    // Single assignment constraints
    //

    // The Englishman lives in the red house.
    simple.addRule(
        same(componentIs<>(house, NATIONALITY, "English"), componentIs<>(house, COLOUR, "Red")));

    // The Spaniard owns the dog.
    simple.addRule(
        same(componentIs<>(house, NATIONALITY, "Spanish"), componentIs<>(house, PET, "Dog")));

    // Coffee is drunk in the green house.
    simple.addRule(
        same(componentIs<>(house, COLOUR, "Green"), componentIs<>(house, DRINK, "Coffee")));

    // The Ukrainian drinks tea.
    simple.addRule(
        same(componentIs<>(house, NATIONALITY, "Ukrainian"), componentIs<>(house, DRINK, "Tea")));

    // 13. The Lucky Strike "Smoke"r "Drink" orange juice.
    simple.addRule(
        same(componentIs<>(house, SMOKE, "Lucky Strike"), componentIs<>(house, DRINK, "Orange Juice")));

    // 14. The Japanese "Smoke" Parliaments.
    simple.addRule(
        same(componentIs<>(house, NATIONALITY, "Japanese"), componentIs<>("Smoke", "Parliaments")));

    // The Old Gold smoker owns snails.
    simple.addRule(
        same(componentIs<>(house, SMOKE, "Old Gold"), componentIs<>(PET, "Snails")));

    // Kools are smoked in the yellow house.
    simple.addRule(
        implies(componentIs<>("Smoke", "Kools"), componentIs<>("Colour", "Yellow")));

    // Milk is drunk in the middle house.
    simple.addRule(
        implies(componentIs < std::string >("Drink", "Milk"), componentIs < std::string >("Position", "3")));

    // The Norwegian lives in the first house.
    simple.addRule(implies(componentIs < std::string >("Nationality", "Norwegian"),
        componentIs < std::string >("Position", "1")));

    //
    // multi assignment constraints 
    //

    // The green house is immediately to the right of the ivory house.
    simple.addRule(
        implies(componentIs<>(COLOUR, "Green"), 
            componentIs<>(POSITION, getComponent<>(componentIs<>(house, COLOUR, "Ivory"), POSITION) + 1 )));

    // The man who smokes Chesterfields lives in the house next to the man with the fox.
    simple.addRule(
        adjacent(orC(componentIs<>(SMOKE, "Chesterfields"), componentIs<>(PET, "Fox"))));

    simple.addRule(
        implies(componentIs<>(SMOKE, "Chesterfields"), notC(componentIs<>(PET, "Fox"))));

    // 12. Kools are smoked in the house next to the house where the horse is kept.
    simple.addRule(
        adjacent(orC(componentIs<>(SMOKE, "Kools"), componentIs<>(PET, "Horse"))));

    simple.addRule(
        implies(componentIs<>(SMOKE, "Kools"), notC(componentIs<>(PET, "Horse"))));

    // 15. The Norwegian lives next to the blue house.
    simple.addRule(
        adjacent(orC(componentIs<>(NATIONALITY, "Norwegian"), componentIs<>(COLOUR, "Blue"))));

    simple.addRule(
        implies(componentIs<>(NATIONALITY, "Norwegian"), notC(componentIs<>(COLOUR, "Blue"))));


    //std::fstream problemFile;
    //problemFile.open("/home/hal/Documents/simple.smt2");
    //simple.print(problemFile);

}