//
// Created by Betrieb-PC on 07.10.2021.
//

#ifndef OMTSCHED_BASICCONDITION_H
#define OMTSCHED_BASICCONDITION_H

#include "../Condition.h"

template<typename ComponentID, typename TagID, typename GroupID>
class ComponentIs : public Condition<ComponentID, TagID, GroupID> {

    ComponentIs(std::string, ComponentID);
    z3::expr instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) = 0;
    //virtual bool evaluate(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) = 0;
    //virtual bool validParameters(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) = 0;

private:
    const std::string componentSlot;

};

ComponentIs<ComponentID, TagID, GroupID>::ComponentIs(std::string componentSlot, ComponentID component) {



}


z3::expr ComponentIs<ComponentID, TagID, GroupID>::instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups){

    //assignment variable equals this value
    return

}

#endif //OMTSCHED_BASICCONDITION_H
