//
// Created by admin on 24.08.2021.
//

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/xml_parser.hpp>
#include <boost/foreach.hpp>
#include "../omtsched.h"
#include "../components/Agent.h"
#include "../components/TimedTask.h"


omtsched::Problem<std::string, std::string, std::string> inrc("INRC2");

using Nurse = omtsched::Agent<std::string, std::string, std::string>;
using Shift = omtsched::TimedTask<std::string, std::string, std::string, int>;

class ShiftAssignment : public Assignment {

public:

    Nurse nurse;
    Shift shift;

    //Formula generate() const override;

};

bool operator<(const ShiftAssignment &lhs, const ShiftAssignment &rhs){
    return lhs.shift < rhs.shift;
}


int main() {

    omtsched::Problem<std::string, std::string, std::string> inrc2;

    namespace pt = boost::property_tree;

    pt::ptree scenarioTree;
    pt::read_xml("/home/hal/Documents/testdatasets_xml/n005w4/Sc-n005w4.xml", scenarioTree);

    //BOOST_FOREACH(pt::ptree::value_type &v, scenarioTree.get_child("Scenario.Skills")) {

    for(pt::ptree::value_type &v : scenarioTree.get_child("Scenario.Skills")){

        std::string skill = v.second.data();
        inrc2.addGroup(skill);

    }

    /* <ShiftTypes>
     *   <ShiftType Id=string>
     *     <NumberOfConsecutiveAssignments>
     *       <Minimum>int
     *       <Maximum>int
     */
    for(pt::ptree::value_type &v : scenarioTree.get_child("Scenario.ShiftTypes")){

        //Id: group

        // Rules for minimum and maximum

    }


/*
// create nurses
for(name) {

    Nurse name (id);

    for(skill) {
        name.addGroup(skill);
    }

    inrc.addComponent(std::move(name));

    // Add contract data

}

// create shifts
for(shift) {

    Shift s (shift);
    s.addGroup(type);

}
 */

}