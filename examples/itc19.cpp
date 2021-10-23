//
// Created by Betrieb-PC on 22.10.2021.
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

int main() {

    omtsched::Problem<std::string> itc19;
    const std::string classType = itc19.addComponentType("C");
    const std::string roomType = itc19.addComponentType("R");
    const std::string studentType = itc19.addComponentType("S");
    const std::string timeType = itc19.addComponentType("T");

    std::string solutionPath;
    std::string problemPath = "C:/Users/Betrieb-PC/Desktop/itc19instances/wbg-fal10.xml";

    pt::ptree scenarioTree;
    pt::read_xml(problemPath, scenarioTree);

    // TODO: Create time

    // Create Rooms
    for(pt::ptree::value_type &room: scenarioTree.get_child("Instance.Resources.Teams")){

        const int &id1 = team1.second.get<int>("<xmlattr>.id");
        const int &id2 = team2.second.get<int>("<xmlattr>.id");
    }

    // Create Courses and Assignments


    // Create Students


};