//
// Created by hal on 01.10.21.
//

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/xml_parser.hpp>
#include "../omtsched.h"
#include "../components/Task.h"
#include "../components/Timeslot.h"
#include "../conditions/BasicConditions.h"
#include "../conditions/BooleanConditions.h"
#include <string>


/*
"CA1 <CA1 teams="0" max="0" mode="H" slots="0" type="HARD"/>
Each team from teams plays at most max home games (mode = "H") or away games
(mode = "A") during time slots in slots. Team 0 cannot play at home on time slot 0.
Each team in teams triggers a deviation equal to the number of home games (mode = "H")
or away games (mode = "A") in slots more than max.
Constraint CA1 is of fundamental use in sports timetabling to model ‘place constraints’ that
forbid a team to play a home game or away game in a given time slot. Constraint CA1 can
also help to balance the home-away status of games over time and teams. For example, when
the home team receives ticket revenues, teams often request to have a limit on the number of
away games they play during the most lucrative time slots. Note that a CA1 constraint where the
set teams contains more than one team can be split into several CA1 constraints where the set
teams contains one team: in all ITC2021 instances, teams therefore contains only one team."
 */
Rule<int> ca1(int team, int max, bool home, std::vector<int> &slots, bool hard){

    auto modeCondition = home ? std::make_unique<ComponentIs<int>>("HomeTeam", team) : std::make_unique<ComponentIs<int>>("AwayTeam", team);

    Condition<std::string>* slotCondition;
    for(const auto &slot : slots)
        slotCondition = Or(ComponentIs("Slot", slot), slotCondition);

    return {MaxAssignments({modeCondition, slotCondition}, max)};

}

int main() {

    omtsched::Problem<std::string, std::string, std::string> itc21;
    std::string solutionPath;
    std::string problemPath;

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

    // A

    // Compactness, P,

    // TODO: phasedness
    // Phased: season is split into two equally long 1RR intervals, where each pair plays
    // in one home-away configuration in both phases
    bool &phased = scenarioTree.get<std::string>("Instance.Structure.Format.gameMode") == "P";
    if(phased){
        //addRule();
    }

    // A timetable is time-constrained (also called compact) if it uses the
    //minimal number of time slots needed, and is time-relaxed otherwise.
    bool &compact = scenarioTree.get<std::string>("Instance.Structure.Format.compactness") == "C";
    if(compact){
        //addRule();
    }

    // Set Objective: minimize number of violated soft constraints, equally weighted

    // Add Constraints
    for(pt::ptree::value_type &node : scenarioTree.get_child("Instance.Constraints.CapacityConstraints")){

        std::string type = ;

        switch (condition) {

            case "CA1":
                bool hard = node.second.get<std::string>("<xmlattr>.type") == "HARD";
                int team = node.second.get<int>("<xmlattr>.teams");
                //std::vector<int> slots;
                int penalty = node.second.get<int>("<xmlattr>.penalty");
                bool home = node.second.get<std::string>("<xmlattr>.mode") == "H";
                int max = node.second.get<int>("<xmlattr>.max");
                itc21.addRule(ca1(team, max, home, slots, hard));
                break;

            case "CA2":
                break;

            case "CA3":
                break;

            case "CA4":
                break;

        }

    }



    // Translate and solve
    TranslatorZ3 z3trans {itc21};
    Model solution {itc21};
    z3trans.getModel(solution);

    // Print solution
    pt::ptree solutionTree;

    solutionTree.put("Solution.MetaData.InstanceName", instanceName);
    solutionTree.put("Solution.MetaData.SolutionName", instanceName + "_sol");

    solutionTree.put("Solution.MetaData.ObjectiveValue.<xmlattr>.infeasibility", 0);
    solutionTree.put("Solution.MetaData.ObjectiveValue.<xmlattr>.objective", model.getPenalty());

    /*
    for(assignment : model.getAssignments())
        for(game : ) {
            solutionTree.put("Solution.Games.ScheduledMatch.<xmlattr>.home", game.homeTeam());
            solutionTree.put("Solution.Games.ScheduledMatch.<xmlattr>.away", game.awayTeam());
            solutionTree.put("Solution.Games.ScheduledMatch.<xmlattr>.slot", game.timeslot());
        }
*/
    pt::write_xml(solutionPath, solutionTree);

}