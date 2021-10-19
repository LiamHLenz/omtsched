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

enum Mode {
    H, A, HA
};

// Utility function to break up strings specifying a set of integer identifiers (e.g. "9;14;5")
std::vector<int> split(const std::string &str){

    std::vector<int> v;
    std::string buffer = "";
    for(const char &c : str) {
        if(c != ';')
            buffer.append(1, c);
        else{
            v.push_back(std::stoi(buffer));
            buffer = "";
        }
    }
    return v;
}

/*
"CA1 <CA1 teams="0" max="0" mode="H" slots="0" type="HARD"/>
Each team from teams plays at most max home games (mode = "H") or away games
(mode = "A") during time slots in slots.
 */
//TODO: punish every violated instance
void ca1(omtsched::Problem<std::string> &pr, std::string team, int max, bool home, std::string &slots, bool hard){

    auto modeCondition = home ? ComponentIs("HomeTeam", team) : ComponentIs("AwayTeam", team);

    Or slotCondition;
    for(const auto &slot : slots)
        slotCondition.add(ComponentIs("Slot", std::string(1, slot)));

    pr.addRule(MaxAssignment({modeCondition, slotCondition}, max));
}

/*
 * CA2 <CA2 teams1="0" min="0" max="1" mode1="HA" mode2="GLOBAL" teams2="1;2"
slots ="0;1;2" type="SOFT"/>
Each team in teams1 plays at most max home games (mode1 = "H"), away games (mode1 =
"A"), or games (mode1 = "HA") against teams (mode2 = "GLOBAL"; the only mode we
consider) in teams2 during time slots in slots.
 */


/*
 * CA3 <CA3 teams1="0" max="2" mode1="HA" teams2="1;2;3" intp="3" mode2=
"SLOTS" type="SOFT"/>
Each team in teams1 plays at most max home games (mode1 = "H"), away games (mode1 =
"A"), or games (mode1 = "HA") against teams in teams2 in each sequence of intp time
slots (mode2 = "SLOTS"; the only mode we consider).
 */


/*
 * CA4 <CA4 teams1="0;1" max="3" mode1="H" teams2="2,3" mode2="GLOBAL"
slots ="0;1" type="HARD"/>
Teams in teams1 play at most max home games (mode1 = "H"), away games (mode1 =
"A"), or games (mode1 = "HA") against teams in teams2 during time slots in slots
(mode2 = "GLOBAL") or during each time slot in slots (mode2 = "EVERY").
 */


/*
 * GA1 <GA1 min="0" max="0" meetings="0,1;1,2;" slots="3" type="HARD"/>
At least min and at most max games from G = {(i1,j1),(i2,j2),...}take place during time
slots in slots. Game (0,1) and (1,2) cannot take place during time slot 3.
The set slots triggers a deviation equal to the number of games in meetings less than min
or more than max.
 */

/*
 * BR1 <BR1 teams="0" intp="0" mode2="HA" slots="1" type="HARD"/>
Each team in teams has at most intp home breaks (mode2 = "H"), away breaks (mode2 =
"A"), or breaks (mode2 = "HA") during time slots in slots. Team 0 cannot have a break
on time slot 1
 */

/*
 * BR2 <BR2 homeMode="HA" teams="0;1" mode2="LEQ" intp="2" slots="0;1;2;3" type="HARD
"/>
The sum over all breaks (homeMode = "HA", the only mode we consider) in teams is no
more than (mode2 = "LEQ", the only mode we consider) intp during time slots in slots.
Team 0 and 1 together do not have more than two breaks during the first four time slots
 */

/*
 * FA2 <FA2 teams="0;1;2" mode="H" intp="1" slots=" 0;1;2;3 " type="HARD"/>
Each pair of teams in teams has a difference in played home games (mode = "H", the only
mode we consider) that is not larger than intp after each time slot in slots. The difference
in home games played between the first three teams is not larger than 1 during the first four
time slots.
 */

/*
 * SE1 <SE1 teams="0;1" min="5" mode1="SLOTS" type="HARD"/>
Each pair of teams in teams has at least min time slots (mode1 = "SLOTS", the only mode
we consider) between two consecutive mutual games. There are at least 5 time slots between
the mutual games of team 0 and 1
 */



int main() {


    omtsched::Problem<std::string> itc21;

    const std::string gameType = itc21.addComponentType("G");
    const std::string slotType = itc21.addComponentType("S");

    std::string solutionPath;
    std::string problemPath;

    namespace pt = boost::property_tree;

    pt::ptree scenarioTree;
    pt::read_xml("C:/Users/Betrieb-PC/Desktop/TestInstances_V3/ITC2021_Test1.xml", scenarioTree);


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

            auto &game = itc21.newComponent(gameID, gameType);

            game.addGroup("h" + std::to_string(id1));       // h: home
            game.addGroup("a" + std::to_string(id2));       // a: away
            game.addGroup("l" + std::to_string(league1));   // l: league
            game.addGroup("p" + std::to_string(id1));       // p: player
            game.addGroup("p" + std::to_string(id2));
        }

    // Create Timeslots and Assignments
    for(pt::ptree::value_type &node: scenarioTree.get_child("Instance.Resources.Slots")){

        const int &id = node.second.get<int>("<xmlattr>.id");
        auto &ts = itc21.newComponent(std::to_string(id), slotType);
        ts.addGroup(std::to_string(id));

        // Create game assignments as fixed timeslot assignments
        auto &gameSlot = itc21.newAssignment();
        gameSlot.setFixed("s_" + std::to_string(id), ts);

        //gameSlot.add("slot_" + std::to_string(id), Game, ANY, true);
    }



    // -----------------------------------------------
    // Add Standard Rules:

    // a team can only play one game simultaneously
    for()
        itc21.addRule( Implies(SameComponent(slotType), Not() ) );


    // TODO: phasedness
    // Phased: season is split into two equally long 1RR intervals, where each pair plays
    // in one home-away configuration in both phases
    bool phased = scenarioTree.get<std::string>("Instance.Structure.Format.gameMode") == "P";
    if(phased){
        //addRule();
    }

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

        // CA1, CA2, CA3, CA4,
        // GA1, BR1, BR2,
        // FA2, SE1
        // TODO: oh my god burn this and burn me
        if(name == "CA1") {
            bool hard = node.second.get<std::string>("<xmlattr>.type") == "HARD";
            std::string team = node.second.get<std::string>("<xmlattr>.teams");
            std::string slots = node.second.get<std::string>("<xmlattr>.slots");
            int penalty = node.second.get<int>("<xmlattr>.penalty");
            bool home = node.second.get<std::string>("<xmlattr>.mode") == "H";
            int max = node.second.get<int>("<xmlattr>.max");
            ca1(itc21, team, max, home, slots, hard);
        }
        else if(name == "CA2") {
        }
        else if(name == "CA3") {
        }
        else if(name == "CA4") {
        }
        else if(name == "GA1") {
        }
        else if(name == "BR1") {
        }
        else if(name == "BR2") {
        }
        else if(name == "FA2") {
        }
        else if(name == "SE1") {
        }
    }


}