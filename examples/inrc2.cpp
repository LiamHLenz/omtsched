//
// Created by admin on 24.08.2021.
//

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/xml_parser.hpp>
#include "../omtsched.h"
#include "../components/Agent.h"
#include "../components/TimedTask.h"


using Nurse = omtsched::Agent<std::string, std::string, std::string>;
using Shift = omtsched::TimedTask<std::string, std::string, std::string, int>;

/*
class ShiftAssignment : public Assignment {

public:

    Nurse nurse;
    Shift shift;

};

bool operator<(const ShiftAssignment &lhs, const ShiftAssignment &rhs){
    return lhs.shift < rhs.shift;
}
*/

int main() {

    omtsched::Problem<std::string, std::string, std::string> inrc2;

    /* ---------------------------------------------
     *          Scenario File
     *          - SCENARIO
     *          - WEEKS
     *          - SKILLS
     *          - SHIFT_TYPES
     *          - FORBIDDEN_SHIFT_TYPES_SUCCESSIONS
     *          - CONTRACTS
     *          - NURSES
     * ----------------------------------------------- */

    //

    namespace pt = boost::property_tree;

    pt::ptree scenarioTree;
    pt::read_xml("/home/hal/Documents/testdatasets_xml/n005w4/Sc-n005w4.xml", scenarioTree);

    // WEEKS
    int weeks = scenarioTree.get<int>("Scenario.NumberOfWeeks");
    std::cout << "Number of weeks: " << weeks << std::endl;

    // SKILLS
    std::cout << "Skills: " << std::endl;
    for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.Skills")) {

        std::string skill = v.second.data();
        inrc2.addGroup(skill);
        std::cout << skill << std::endl;
    }

    /* SHIFT TYPES
     * <ShiftTypes>
     *   <ShiftType Id=string>
     *     <NumberOfConsecutiveAssignments>
     *       <Minimum>int
     *       <Maximum>int
     */
    for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.ShiftTypes")) {

        //Id: group
        std::string type = v.second.get<std::string>("<xmlattr>.Id");
        inrc2.addGroup(type);
        std::cout << type << std::endl;

        int min = v.second.get<int>("NumberOfConsecutiveAssignments.Minimum");
        int max = v.second.get<int>("NumberOfConsecutiveAssignments.Maximum");

        std::cout << "Minimum: " << min << std::endl;
        std::cout << "Maximum: " << max << std::endl;

        // Min and Max consecutive
        inrc2.addRule("MaxConsecutive(A1.nurse == A2.nurse, A1.inGroup(" + type + ") && A2.inGroup(" + type + "), " +
                      std::to_string(max) + ")");
        inrc2.addRule("MinConsecutive(A1.nurse == A2.nurse, A1.inGroup(" + type + ") && A2.inGroup(" + type + "), " +
                      std::to_string(min) + ")");
        //TODO: consecutive rules have primary and secondary conditions (for constructing bvs)

    }

    // <ForbiddenShiftTypeSuccessions>
    //        <ShiftTypeSuccession>
    //            <PrecedingShiftType>Type1</PrecedingShiftType>
    //            <SucceedingShiftTypes>
    //                <ShiftType>Type2</ShiftType>
    for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.ForbiddenShiftTypeSuccessions")) {

        std::string precType = v.second.get<std::string>("PrecedingShiftType");
        std::cout << "Predecessor shift type: " << precType << std::endl;

        for (boost::property_tree::ptree::value_type const &w: v.second.get_child("SucceedingShiftTypes")) {
            std::string sucType = w.second.get<std::string>("");
            std::cout << "Successor shift type: " << sucType << std::endl;
            inrc2.addRule("!(A1.Nurse == A2.Nurse && ImmediateSuccessor(A1, A2) && A1.inGroup(" + precType +
                          ") && A2.inGroup(" + sucType + "))");
        }

    }


// Add nurses as components
    for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.Nurses")) {


        std::string id = v.second.get<std::string>("<xmlattr>.Id");
        std::cout << "Nurse name: " << id << std::endl;
        Nurse nurse(id);

        for (boost::property_tree::ptree::value_type const &w: v.second.get_child("Skills")) {
            const auto &skill = w.second.get<std::string>("");
            std::cout << "Nurse skill: " << skill << std::endl;
            nurse.addGroup(skill);
        }

        inrc2.addComponent(nurse);


        // Add contract data
        std::string contract = v.second.get<std::string>("Contract");
        std::cout << "Nurse contract: " << contract << std::endl;
        for (pt::ptree::value_type &v: scenarioTree.get_child("Scenario.Contracts")) {

            if (v.second.get<std::string>("<xmlattr>.Id") == contract) {

                int min = v.second.get<int>("NumberOfAssignments.Minimum");
                int max = v.second.get<int>("NumberOfAssignments.Maximum");
                inrc2.addRule("MinAssigned(A.Nurse == " + id + ", " + std::to_string(min) + ")");
                inrc2.addRule("MaxAssigned(A.Nurse == " + id + ", " + std::to_string(max) + ")");

                //TODO: define consecutive
                min = v.second.get<int>("ConsecutiveWorkingDays.Minimum");
                max = v.second.get<int>("ConsecutiveWorkingDays.Maximum");
                inrc2.addRule("MinConsecutive(A.Nurse == " + id + ", " + std::to_string(min) + ")");
                inrc2.addRule("MaxConsecutive(A.Nurse == " + id + ", " + std::to_string(max) + ")");

                //TODO: define consecutive
                min = v.second.get<int>("ConsecutiveDaysOff.Minimum");
                max = v.second.get<int>("ConsecutiveDaysOff.Maximum");
                inrc2.addRule("MinBreak(A.Nurse == " + id + ", " + std::to_string(min) + ")");
                inrc2.addRule("MaxBreak(A.Nurse == " + id + ", " + std::to_string(max) + ")");

                //TODO: working weekends: max and full-weekends
                max = v.second.get<int>("MaximumNumberOfWorkingWeekends");
                //inrc2.addRule("MaxAssignments(A.Nurse == "+id+", )");

                //TODO: complete weekends

                break;
            }
        }
    }

}


// Create the week
void createWeek(const std::string &path){

    

}