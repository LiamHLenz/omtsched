//
// Created by hal on 07.09.21.
//

#ifndef OMTSCHED_CONDITION_H
#define OMTSCHED_CONDITION_H

#include <z3.h>
#include <z3++.h>
#include "ComponentType.h"
#include "Component.h"

template<typename ID>
class Condition {

public:
    virtual z3::expr instantiate(const std::vector<const std::vector< const Assignment<ID>*>>& assignmentGroups) = 0;
    //virtual bool evaluate(std::vector<Component<ID>*>& arguments) = 0;
    //virtual bool validParameters(std::vector<Component<ID>*>& arguments) = 0;

private:
    // specifies the types of
    std::vector<ComponentType> paramenterTypes;
    std::vector<Condition*> subconditions;

};


// ------------------------------------
// OR, AND,

//class NumAssigned


template<typename ID>
class MaxAssignment : public Condition<ID>{

    MaxAssignment(std::vector<Condition<ID>>, const int&);
    virtual z3::expr instantiate(const std::vector<const std::vector<const Assignment<ID>*>>& assignmentGroups) override;

private:
    std::vector<Condition<ID>> conditions;

};
/*
template<typename ID>
MaxAssignment<ID>::MaxAssignment(std::vector<Condition<ID>> c, const int& m) :  {};

template<typename ID>
z3::expr MaxAssignment<ID>::instantiate(const std::vector<const std::vector< const Assignment<ID>*>>& assignmentGroups) {

    /*
     * Resolved by:
     * 1. creating a bitvector of (relevant) assignments
     * 2. creating an implication for each assignment: if the conditions are met the
     *    bit corresponding to the assignment is set
     * 3. constraining the maximum number of set bits
     /

    //
}
*/
#endif //OMTSCHED_CONDITION_H
