//
// Created by Betrieb-PC on 25.10.2021.
//

#ifndef OMTSCHED_CONDITIONSZ3_H
#define OMTSCHED_CONDITIONSZ3_H

#include "TranslatorZ3.h"

template<typename ID>
z3::expr TranslatorZ3::resolveCondition(const Condition <ID> &condition, const std::vector<Assignment<ID>*> asgnComb){
    //TODO: resolve condition
}


template<typename ID>
z3::expr omtsched::TranslatorZ3<ID>::resolveComponentIs(const omtsched::ComponentIs<ID> &,
                                                        const omtsched::Assignment<ID> *asgn) {
    const z3::expr &component = getConstant(c.component);
    const z3::expr &var = getVariable(*asgn, c.componentSlot, 1);
    return var == component;

}

template<typename ID>
z3::expr TranslatorZ3::resolveComponentIn(const ComponentIn <ID> &, const Assignment<ID>* asgn);

template<typename ID>
z3::expr TranslatorZ3::resolveSameComponent(const SameComponent <ID> &, const std::vector<Assignment<ID>*> asgnComb);

template<typename ID>
z3::expr TranslatorZ3::resolveInGroup(const InGroup <ID> &, const Assignment<ID> asgn);

template<typename ID>
z3::expr TranslatorZ3::resolveMaxAssignments(const MaxAssignment <ID> &, const std::vector<Assignment<ID>*> asgnComb);

#endif //OMTSCHED_CONDITIONSZ3_H
