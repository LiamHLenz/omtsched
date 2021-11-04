//
// Created by hal on 01.10.21.
//

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/xml_parser.hpp>
#include "../omtsched.h"
#include <string>

using And = omtsched::And<std::string>;
using Or = omtsched::Or<std::string>;
using ComponentIs = omtsched::ComponentIs<std::string>;
using MaxAssignment = omtsched::MaxAssignment<std::string>;
using Condition = omtsched::Condition<std::string>;
using InGroup = omtsched::InGroup<std::string>;
using SameComponent = omtsched::SameComponent<std::string>;
using ComponentIn = omtsched::ComponentIn<std::string>;

namespace pt = boost::property_tree;

// Utility function to break up strings specifying a set of integer identifiers (e.g. "9;14;5")
std::vector<std::string> split(const std::string &str){

    std::vector<std::string> v;
    std::string buffer = "";
    for(const char &c : str) {
        if(c != ';')
            buffer.append(1, c);
        else{
            v.push_back(buffer);
            buffer = "";
        }
    }
    return v;
}

// Utility functions for retrieving values of IDs from a property tree
std::vector<std::string> fetchIDs(const pt::ptree::value_type &node, const std::string &name) {

    const std::string &s = node.second.get_optional<std::string>("<xmlattr>."+name).get_value_or("");
    return split(s);
}

std::string fetchString(const pt::ptree::value_type &node, const std::string &name) {
    return node.second.get_optional<std::string>("<xmlattr>."+name).get_value_or("");
}

int fetchInt(const pt::ptree::value_type &node, const std::string &name) {
    return node.second.get_optional<int>("<xmlattr>."+name).get_value_or(0);
}


int main() {

    omtsched::Problem<std::string> itc21;

    const std::string gameType = itc21.addComponentType("G");
    const std::string slotType = itc21.addComponentType("S");

    std::string solutionPath;
    std::string problemPath;

    pt::ptree scenarioTree;
    pt::read_xml("C:/Users/Betrieb-PC/Desktop/TestInstances_V3/ITC2021_Test3.xml", scenarioTree);


    // Create Games
    // Create one game for every combination of teams (except identical)
    for(pt::ptree::value_type &team1: scenarioTree.get_child("Instance.Resources.Teams"))
        for(pt::ptree::value_type &team2: scenarioTree.get_child("Instance.Resources.Teams")){

            const int &id1 = team1.second.get<int>("<xmlattr>.id");
            const int &id2 = team2.second.get<int>("<xmlattr>.id");

            const int &league1 = team1.second.get<int>("<xmlattr>.league");
            const int &league2 = team2.second.get<int>("<xmlattr>.league");

            if(id1 == id2 || league1 != league2)
                continue;

            std::string gameID = std::to_string(id1) + "_" + std::to_string(id2);

            auto &game = itc21.newComponent(gameID, gameType);

            game.addGroup("H" + std::to_string(id1));       // h: home
            game.addGroup("A" + std::to_string(id2));       // a: away
            game.addGroup("l" + std::to_string(league1));   // l: league
            game.addGroup("HA" + std::to_string(id1));       // p: player
            game.addGroup("HA" + std::to_string(id2));
        }

    // Create Timeslots and Assignments
    for(pt::ptree::value_type &node: scenarioTree.get_child("Instance.Resources.Slots")){

        const int &id = node.second.get<int>("<xmlattr>.id");
        auto &ts = itc21.newComponent(std::to_string(id), slotType);
        ts.addGroup(std::to_string(id));

        // Create game assignments as fixed timeslot assignments
        auto &gameSlot = itc21.newAssignment();
        gameSlot.setFixed("s_" + std::to_string(id), ts);

        gameSlot.setVariable("slot_" + std::to_string(id), gameType, omtsched::Number::ANY, true);
    }

    // -----------------------------------------------
    //           Add Implicit Rules:

    // a team can only play one game simultaneously
    //for(pt::ptree::value_type &team1: scenarioTree.get_child("Instance.Resources.Teams")){
    //    itc21.addRule( Implies(SameComponent(slotType), Not(Overlap()) ) );


    // TODO: phasedness
    // Phased: season is split into two equally long 1RR intervals, where each pair plays
    // in one home-away configuration in both phases
    bool phased = scenarioTree.get<std::string>("Instance.Structure.Format.gameMode") == "P";
    if(phased){
        //addRule();
    }

    // TODO: compacted-ness
    // A timetable is time-constrained (also called compact) if it uses the
    //minimal number of time slots needed, and is time-relaxed otherwise.
    bool compact = scenarioTree.get<std::string>("Instance.Structure.Format.compactness") == "C";
    if(compact){
        //addRule();
    }

    // Set Objective: minimize number of violated soft constraints, equally weighted

    // Add Constraints
    for(pt::ptree::value_type &node : scenarioTree.get_child("Instance.Constraints.CapacityConstraints")){

        std::string name = node.first;

        bool hard = node.second.get<std::string>("<xmlattr>.type") == "HARD";

        // Collecting all possibly used values in one plac,
        // since most of them are used in multiple rules
        auto teams = fetchIDs(node, "teams");
        auto teams1 = fetchIDs(node, "teams1");
        auto teams2 = fetchIDs(node, "teams2");
        auto slots = fetchIDs(node, "slots");

        std::string mode = fetchString(node, "mode");
        std::string mode1 = fetchString(node, "mode1");
        std::string mode2 = fetchString(node, "mode2");
        std::string homeMode = fetchString(node, "homeMode");

        int penalty = fetchInt(node, "penalty");
        int min = fetchInt(node, "min");
        int max = fetchInt(node, "max");
        int intp = fetchInt(node, "intp");

        // Meetings
        std::string meetings = node.second.get_optional<std::string>("<xmlattr>.meetings").get_value_or("");


        if(name == "CA1") {
            // team plays at most max home or away games (mode = "A") during time slots in slots
            std::string team = teams.at(0);
            itc21.addRule( MaxAssignment( max, {InGroup(gameType, mode+team), ComponentIn(slotType, slots)}), hard, 1);
        }
        else if(name == "CA2") {
            // team plays at most max home, away, or games (mode1 = "HA") against teams in teams2 during time slots in slots
            std::string team = teams1.at(0);

            Condition t2Con;
            for(std::string t : teams2)
                t2Con = Or({t2Con, InGroup(gameType, "HA"+t)});

            itc21.addRule( MaxAssignment(max, {InGroup(gameType, mode+team), t2Con, ComponentIn(slotType, slots)}), hard, 1);
        }
        else if(name == "CA3") {
            // Each team in teams1 plays at most max home games, away games, or games ( against teams
            // in teams2 in each sequence of intp time slots

            Condition t2Con;
            for(std::string t : teams2)
                t2Con = Or({t2Con, InGroup(gameType, "HA"+t)});

            for(const std::string team : teams1)
                itc21.addRule( MaxInSequence(max, intp, InGroup(gameType, mode1+team), t2Con), hard, 1);
        }
        else if(name == "CA4") {
            // Teams in teams1 play at most max home games (mode1 = "H"), away games (mode1 =
            //"A"), or games (mode1 = "HA") against teams in teams2 during time slots in slots
            //(mode2 = "GLOBAL") or during each time slot in slots (mode2 = "EVERY").
            // Need to sum conditions
        }
        else if(name == "GA1") {
            // not needed yet
        }
        else if(name == "BR1") {
            // team has at most intp home breaks, away breaks, or breaks during time slots in slots
            //std::string team = teams.at(0);
            // summing over consecutives?
            // max with previous status = next status
            // max assignments where the previous timeslot has the same
            //MaxAssignment( SameComponent(Previous(), ) )
        }
        else if(name == "BR2") {
            // not needed yet
        }
        else if(name == "FA2") {
            // Each pair of teams in teams has a difference in played home games (mode = "H", the only
            // mode we consider) that is not larger than intp after each time slot in slots.

        }
        else if(name == "SE1") {
            // not needed yet
        }
    }


}