//
// Created by hal on 07.09.21.
//

#ifndef OMTSCHED_CONDITION_H
#define OMTSCHED_CONDITION_H

#include <z3.h>
#include <z3++.h>
#include "ComponentType.h"
#include "Component.h"

template<typename ComponentID, typename TagID, typename GroupID>
class Condition {

public:
    virtual z3::expr instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) = 0;
    virtual bool evaluate(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) = 0;
    virtual bool validParameters(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) = 0;

private:
    // specifies the types of
    std::vector<ComponentType> paramenterTypes;
    std::vector<Condition*> subconditions;

};


// ------------------------------------
// OR, AND,

class NumAssigned 
*/

template<typename ComponentID, typename TagID, typename GroupID>
class MaxAssignment : public Condition<ComponentID, TagID, GroupID>{

    MaxAssignment(std::vector<Condition>, const int&);
    virtual z3::expr instantiate(const std::vector<const std::vector<const Assignment*>>& assignmentGroups) override;

private:
    std::vector<Condition> conditions;

};

template<typename ComponentID, typename TagID, typename GroupID>
MaxAssignment<ComponentID, TagID, GroupID>::MaxAssignment(std::vector<Condition> c, const int& m) :  {};

template<typename ComponentID, typename TagID, typename GroupID>
MaxAssignment<ComponentID, TagID, bool GroupID>::z3::expr instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) {

    /*
     * Resolved by:
     * 1. creating a bitvector of (relevant) assignments
     * 2. creating an implication for each assignment: if the conditions are met the
     *    bit corresponding to the assignment is set
     * 3. constraining the maximum number of set bits
     */

    //
}

#endif //OMTSCHED_CONDITION_H
