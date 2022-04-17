//
// Created by hal on 05.11.21.
//

#include "../omtsched.h"
#include "../conditions/OrderedConditions.h"
#include <initializer_list>
#include <fstream>

void getZebra(omtsched::Problem<std::string> &simple) {

    using namespace omtsched;

    const auto &colourT = simple.addComponentType("C");
    for (std::string str: {"Yellow", "Blue", "Red", "Ivory", "Green"})
        simple.newComponent(str, colourT);

    const auto &nationT = simple.addComponentType("N");
    for (std::string str: {"English", "Spanish", "Norwegian", "Ukrainian", "Japanese"})
        simple.newComponent(str, nationT);

    const auto &drinkT = simple.addComponentType("D");
    for (std::string str: {"Water", "Tea", "Milk", "Orange Juice", "Coffee"})
        simple.newComponent(str, drinkT);

    const auto &smokeT = simple.addComponentType("S");
    for (std::string str: {"Kools", "Chesterfields", "Lucky Strike", "Parliaments", "Old Gold"})
        simple.newComponent(str, smokeT);

    const auto &petT = simple.addComponentType("Pet");
    for (std::string str: {"Zebra", "Fox", "Horse", "Snails", "Dog"})
        simple.newComponent(str, petT);

    const auto &positionT = simple.addComponentType("P");
    for (std::string str: {"1", "2", "3", "4", "5"}) {

        const auto &position = simple.newOrderedComponent(str, positionT, std::stoi(str));

        auto &asgn = simple.newAssignment(str);
        asgn.setFixed("Position", position);
        asgn.setVariable("Colour", colourT, false);
        asgn.setVariable("Nationality", nationT, false);
        asgn.setVariable("Drink", drinkT, false);
        asgn.setVariable("Smoke", smokeT, false);
        asgn.setVariable("Pet", petT, false);
    }

    // All different
    simple.addRule(distinct < std::string > ("Colour"));
    simple.addRule(distinct < std::string > ("Nationality"));
    simple.addRule(distinct < std::string > ("Drink"));
    simple.addRule(distinct < std::string > ("Smoke"));
    simple.addRule(distinct < std::string > ("Pet"));


    // 2. The Englishman lives in the red house.
    //simple.addRule(implies(componentIs < std::string > ("Nationality", "English"),
    //                       componentIs < std::string > ("Colour", "Red")));

    // 3. The Spaniard owns the dog.
    //simple.addRule(implies(componentIs < std::string > ("Nationality", "Spanish"),
    //                       componentIs < std::string > ("Pet", "Dog")));

    // 4. Coffee is drunk in the green house.
    //simple.addRule(
    //        implies(componentIs < std::string > ("Colour", "Green"), componentIs < std::string > ("Drink", "Coffee")));

    // 5. The Ukrainian "Drink" tea.
    //simple.addRule(implies(componentIs < std::string > ("Nationality", "Ukrainian"),
    //                       componentIs < std::string > ("Drink", "Tea")));

    // 6. The green house is immediately to the right of the ivory house.
    std::string slot = "Position";
    simple.addRule(blocked(slot, {orC<std::string>(
            {componentIs < std::string > ("Colour", "Green"), componentIs < std::string > ("Colour", "Ivory")})}));
    //simple.addRule(greater("Position", componentIs<std::string>("Colour", "Green"), componentIs<std::string>("Colour", "Ivory")));

    // 7. The Old Gold "Smoke"r owns snails.
    //simple.addRule(
    //        implies(componentIs < std::string > ("Smoke", "Old Gold"), componentIs < std::string > ("Pet", "Snails")));

    // 8. Kools are "Smoke"d in the yellow house.
    //simple.addRule(
    //        implies(componentIs < std::string > ("Smoke", "Kools"), componentIs < std::string > ("Colour", "Yellow")));

    // 9. Milk is drunk in the middle house.
    //simple.addRule(
    //        implies(componentIs < std::string > ("Drink", "Milk"), componentIs < std::string > ("Position", "3")));

    // 10. The Norwegian lives in the first house.
    //simple.addRule(implies(componentIs < std::string > ("Nationality", "Norwegian"),
    //                       componentIs < std::string > ("Position", "1")));

    // 11. The man who "Smoke" Chesterfields lives in the house next to the man with the fox.
    //simple.addRule(blocked("Position", componentIs<std::string>("Smoke", "Chesterfields"), componentIs<std::string>("Pet", "Fox")));

    // 12. Kools are "Smoke"d in the house next to the house where the horse is kept.
    //simple.addRule(blocked("Position", componentIs<std::string>("Smoke", "Kools"), componentIs<std::string>("Pet", "Horse")));

    // 13. The Lucky Strike "Smoke"r "Drink" orange juice.
    //simple.addRule(implies(componentIs < std::string > ("Smoke", "Lucky Strike"),
    //                       componentIs < std::string > ("Drink", "Orange Juice")));

    // 14. The Japanese "Smoke" Parliaments.
    //simple.addRule(implies(componentIs < std::string > ("Nationality", "Japanese"),
    //                       componentIs < std::string > ("Smoke", "Parliaments")));

    // 15. The Norwegian lives next to the blue house.
    //simple.addRule(blocked("Position", componentIs<std::string>("Nationality", "Norwegian"), componentIs<std::string>("Colour", "Blue")));



    //std::fstream problemFile;
    //problemFile.open("/home/hal/Documents/simple.smt2");
    //simple.print(problemFile);

}