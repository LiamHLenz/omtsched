//
// Created by hal on 01.10.21.
//

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/xml_parser.hpp>
#include "../omtsched.h"
#include "../components/Task.h"
#include "../components/Timeslot.h"
#include <string>

int main() {

    omtsched::Problem<std::string, std::string, std::string> itc21;

    namespace pt = boost::property_tree;

    pt::ptree scenarioTree;
    pt::read_xml("/home/hal/Desktop/ITC2021_Test1.xml", scenarioTree);


    // Create Games
    // Create one game for every combination of teams (except identical)
    // TODO: can be made more efficient by handling symmetry
    for(pt::ptree::value_type &team1: scenarioTree.get_child("Instance.Resources.Teams"))
        for(pt::ptree::value_type &team2: scenarioTree.get_child("Instance.Resources.Teams")){

            const int &id1 = team1.second.get<int>("<xmlattr>.id");
            const int &id2 = team2.second.get<int>("<xmlattr>.id");

            const int &league1 = team1.second.get<int>("<xmlattr>.league");
            const int &league2 = team2.second.get<int>("<xmlattr>.league");

            if(id1 == id2 || league1 != league2)
                continue;

            std::string gameID = std::to_string(id1) + "_" + std::to_string(id2);

            auto game = itc21.newComponent(Game, gameID);

            game.addGroup("h" + std::to_string(id1));       // h: home
            game.addGroup("a" + std::to_string(id2));       // a: away
            game.addGroup("l" + std::to_string(league1));   // l: league
            game.addGroup("p" + std::to_string(id1));       // p: player
            game.addGroup("p" + std::to_string(id2));
        }

    // Create Timeslots and Assignments
    for(pt::ptree::value_type &node: scenarioTree.get_child("Instance.Resources.Slots")){

        const int &id = node.second.get<int>("<xmlattr>.id");
        auto ts = itc21.newComponent(Timeslot, id);
        ts.addGroup(std::to_string(id));

        // Create game assignments as fixed timeslot assignments
        auto gameSlot = itc21.newAssignment();
        gameSlot.setFixed(ts);
        gameSlot.setVariable(Game, ANY, true);
    }

    // Add Standard Rules:
    // Compactness, P,
    if()

    // Set Objective

    // Add Constraints


}