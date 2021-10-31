//
// Created by admin on 24.08.2021.
//

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/xml_parser.hpp>
#include "../omtsched.h"

using namespace omtsched;

int main() {

    using CondPtr = std::shared_ptr<Condition<std::string>>;

    omtsched::Problem<std::string> inrc2;

    const std::string nurseType = inrc2.addComponentType("N");
    const std::string timeType = inrc2.addComponentType("T");

    const std::string &nurseSlot = "Nurse";
    const std::string &timeSlot = "Time";

    namespace pt = boost::property_tree;

    pt::ptree scenarioTree;
    pt::read_xml("C:/Users/Betrieb-PC/Desktop/testdatasets_xml/n005w4/Sc-n005w4.xml", scenarioTree);

    int weeks = scenarioTree.get<int>("Scenario.NumberOfWeeks");

    // SKILLS
    for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.Skills")) {

        std::string skill = v.second.data();
        inrc2.addGroup(skill);
    }

    // SHIFT TYPES
    for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.ShiftTypes")) {

        std::string type = v.second.get<std::string>("<xmlattr>.Id");
        inrc2.addGroup(type);

        int min = v.second.get<int>("NumberOfConsecutiveAssignments.Minimum");
        int max = v.second.get<int>("NumberOfConsecutiveAssignments.Maximum");

        // Min and Max consecutive
        //inrc2.addRule(MaxConsecutive(max, , {SameComponent("Nurse"), InGroup("Time", type)}));
        //inrc2.addRule(MinConsecutive(min, , {SameComponent("Nurse"), InGroup("Time", type)}));

    }

    // ForbiddenShiftTypeSuccessions
/*    for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.ForbiddenShiftTypeSuccessions")) {

        std::string precType = v.second.get<std::string>("PrecedingShiftType");
        std::cout << "Predecessor shift type: " << precType << std::endl;

        for (boost::property_tree::ptree::value_type const &w: v.second.get_child("SucceedingShiftTypes")) {
            std::string sucType = w.second.get<std::string>("");
            std::cout << "Successor shift type: " << sucType << std::endl;
            inrc2.addRule("!(A1.Nurse == A2.Nurse && ImmediateSuccessor(A1, A2) && A1.inGroup(" + precType +
                          ") && A2.inGroup(" + sucType + "))");
        }

    }*/


    // Add nurses as components
    for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.Nurses")) {

        std::string id = v.second.get<std::string>("<xmlattr>.Id");

        auto &nurse = inrc2.newComponent(id, nurseType);

        for (boost::property_tree::ptree::value_type const &w: v.second.get_child("Skills")) {
            const auto &skill = w.second.get<std::string>("");
            nurse.addGroup(skill);
        }

        // Add contract data
        std::string contract = v.second.get<std::string>("Contract");
        for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.Contracts")) {

            if (v.second.get<std::string>("<xmlattr>.Id") == contract) {

                // Maximum and Minimum total number of assignments
                int min = v.second.get<int>("NumberOfAssignments.Minimum");
                int max = v.second.get<int>("NumberOfAssignments.Maximum");

                inrc2.addRule(maxAssignment<std::string>( max, {componentIs(nurseSlot, id)}), false, 0);
                inrc2.addRule(minAssignment<std::string>( min, {componentIs(nurseSlot, id)}), false, 0);

                // Maximum and Minimum consecutive work days
                min = v.second.get<int>("ConsecutiveWorkingDays.Minimum");
                max = v.second.get<int>("ConsecutiveWorkingDays.Maximum");
                inrc2.addRule(maxConsecutive( max, timeSlot, {componentIs(nurseSlot, id)} ), false, 0);
                inrc2.addRule(minConsecutive( min, timeSlot, {componentIs(nurseSlot, id)} ), false, 0);

                // Maximum and Minimum consecutive days off
                min = v.second.get<int>("ConsecutiveDaysOff.Minimum");
                max = v.second.get<int>("ConsecutiveDaysOff.Maximum");
                inrc2.addRule(MaxBreak( max, timeSlot, {componentIs(nurseSlot, id)} ), false, 0);
                inrc2.addRule(MinBreak( min, timeSlot, {componentIs(nurseSlot, id)} ), false, 0);
            /*
                //TODO: working weekends: max and full-weekends
                max = v.second.get<int>("MaximumNumberOfWorkingWeekends");
                /*
                std::vector<Condition<std::string>> workingWeekends;
                workingWeekends.push_back(ComponentIs<std::string>("Nurse", nurse));
                for(int num = 0; num < weeks; num++)
                    workingWeekends.emplace_back(Or(InGroup<std::string>("Time", "Saturday"+num), InGroup<std::string>("Time", "Sunday"+num)));

                inrc2.addRule(MaxAssignment(max, workingWeekends));

                // Complete Weekends are given as 0 or 1
                bool completeWE = v.second.get<int>("CompleteWeekends");
                if(completeWE){

                    for(int num = 0; num < weeks; num++) {

                        inrc2.addRule( Implies(And(ComponentIs("Nurse", nurse), InGroup("Time", "Saturday"+num)),
                                               MinAssignment(1, And(ComponentIs("Nurse", nurse), InGroup("Time", "Sunday"+num))) ));

                        inrc2.addRule( Implies(And(ComponentIs("Nurse", nurse), InGroup("Time", "Sunday"+num)),
                                               MinAssignment(1, And(ComponentIs("Nurse", nurse), InGroup("Time", "Saturday"+num))) ));

                    }

                }/
            */
                break;
            }
        }
    }


    // Disregard History
    // Create Weeks
    int dayCounter = 1;
    const std::string &weekPath = "C:/Users/Betrieb-PC/Desktop/testdatasets_xml/n005w4/WD-n005w4-";
    for(int weekCounter = 0; weekCounter < weeks; weekCounter++){

        pt::ptree weekTree;
        pt::read_xml(weekPath+std::to_string(weekCounter)+".xml", weekTree);


        /*
         *  pt::read_xml("C:/Users/Betrieb-PC/Desktop/testdatasets_xml/n005w4/Sc-n005w4.xml", scenarioTree);
            int weeks = scenarioTree.get<int>("Scenario.NumberOfWeeks");
         // SKILLS
        for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.Skills")) {
         */

        // Create the shifts
        for(pt::ptree::value_type &v: weekTree.get_child("WeekData.Requirements")){

            // It is given, for each shift, for each skill, for each week day, the optimal and minimum number
            // of nurses necessary to fulfil the working duties.
            const std::string shiftType = v.second.get<std::string>("ShiftType");
            const std::string skill = v.second.get<std::string>("Skill");

            const std::vector<std::string> weekDayRequirements {"RequirementOnMonday", "RequirementOnTuesday",
                                                          "RequirementOnWednesday", "RequirementOnThursday",
                                                          "RequirementOnFriday", "RequirementOnSaturday", "RequirementOnSunday"};

            for(const std::string &wdr: weekDayRequirements){

                // -<RequirementOnMonday>
                // <Minimum>1</Minimum>
                // <Optimal>1</Optimal>
                const int min = v.second.get<int>(wdr + ".Minimum");
                const int opt = v.second.get<int>(wdr + ".Optimal");

                if(min != 0) {

                    // Create min assignments
                    for(int j = 0; j < min; j++){

                        const std::string name = "w"+std::to_string(weekCounter)+"d"+std::to_string(dayCounter);
                        auto &asgn = inrc2.newAssignment(name);
                        auto &time = inrc2.newComponent(name, timeType);
                        time.addGroup(skill);
                        asgn.setFixed(timeSlot, time);

                        if(dayCounter % 6 == 0)
                            time.addGroup("Saturday" + std::to_string(weekCounter));
                        else if(dayCounter % 7 == 0)
                            time.addGroup("Sunday" + std::to_string(weekCounter));

                        asgn.setVariable(nurseSlot, nurseType, false);
                        asgn.setOptional(false);
                    }

                    if(opt != 0)
                        for(int j = 0; j < min; j++){

                            const std::string name = "w"+std::to_string(weekCounter)+"d"+std::to_string(dayCounter);
                            auto &asgn = inrc2.newAssignment(name);
                            auto &time = inrc2.newComponent(name, timeType);
                            time.addGroup(skill);
                            asgn.setFixed(timeSlot, time);

                            if(dayCounter % 6 == 0)
                                time.addGroup("Saturday" + std::to_string(weekCounter));
                            else if(dayCounter % 7 == 0)
                                time.addGroup("Sunday" + std::to_string(weekCounter));

                            asgn.setVariable(nurseSlot, nurseType, false);
                            asgn.setOptional(true);

                        }
                }

                dayCounter++;
            }

        }

        // Create the shift-off requests
        for(pt::ptree::value_type &v: weekTree.get_child("WeekData.ShiftOffRequests")){

            //inrc2.addRule( , true, )

        }

    }

    std::ofstream solfile;
    solfile.open ("C:/Users/Betrieb-PC/Desktop/testproblem/n005w4.smt2");
    inrc2.print(solfile);
    solfile.close();

    TranslatorZ3 translator (inrc2);
    //translator.solve();

    //Model model = translator.getModel();

    // Generate solution files

}

