//
// Created by Betrieb-PC on 07.10.2021.
//

#ifndef OMTSCHED_BASICCONDITIONS_H
#define OMTSCHED_BASICCONDITIONS_H

#include "../Condition.h"

template<typename ID>
class ComponentIs : public Condition<ID> {

public:
    ComponentIs(std::string, ID);
    z3::expr instantiate(const std::vector<const std::vector< const Assignment<ID>*>>& assignmentGroups);
    //virtual bool evaluate(std::vector<Component<ID>*>& arguments) = 0;
    //virtual bool validParameters(std::vector<Component<ID>*>& arguments) = 0;

private:
    const std::string componentSlot;
    const ID component;
};

template<typename ID>
ComponentIs<ID>::ComponentIs(std::string componentSlot, ID component) : componentSlot{componentSlot}, component{component} {}

template<typename ID>
z3::expr ComponentIs<ID>::instantiate(const std::vector<const std::vector< const Assignment<ID>*>>& assignmentGroups){

    // Sorts!

}

#endif //OMTSCHED_BASICCONDITIONS_H
