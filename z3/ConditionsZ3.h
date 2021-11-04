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
z3::expr omtsched::TranslatorZ3<ID>::resolveComponentIs(const omtsched::ComponentIs<ID> &c,
                                                        const omtsched::Assignment<ID> *asgn) {
    const z3::expr &component = getConstant(c.component);
    const z3::expr &var = getVariable(*asgn, c.componentSlot);
    return var == component;

}

template<typename ID>
z3::expr TranslatorZ3::resolveComponentIn(const ComponentIn <ID> &c, const Assignment<ID>* asgn) {

    z3::expr_vector equalities;
    for(const z3::expr &component : c.components) {

        const z3::expr &var = getVariable(*asgn, c.componentSlot);
        equalities.push_back( var == component );
    }

    return z3::mk_or(equalities);
}

template<typename ID>
z3::expr TranslatorZ3::resolveSameComponent(const SameComponent <ID> &c, const std::vector<Assignment<ID>*> asgnComb) {

    z3::expr_vector equalities;
    for(auto it1 = asgnComb.begin(); it1 != asgnComb.end(); it1++)
        for(auto it2 = it1.next(); it2 != asgnComb.end(); it2++) {

            const z3::expr &var1 = getVariable(*itc1, c.slot);
            const z3::expr &var1 = getVariable(*itc2, c.slot);
            equalities.push_back(var1 == va2);
        }
    return z3::mk_and(equalities);
}

template<typename ID>
z3::expr TranslatorZ3::resolveInGroup(const InGroup <ID> &c, const Assignment<ID> *asgn) {

    /*
     * InGroup(const ID &componentType, ID groupID) : slot{slot}, group{groupID} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::IN_GROUP;
        const ID slot;
        const ID group;
     */

    const z3::expr &var = getVariable(*asgn, c.slot);
    // limits domain
    // get slot type
    const ID &type = asgn->getSlot(slot).type;

    // std::map<ID, std::vector<Component<ID>>> components;
    z3::expr_vector equalities;
    for(const Component<ID> &component : this->problem.getComponents(type)){

        if(component.inGroup(c.group)) {
            const z3::expr &comp = getConstant(component.getID());
            equalities.push_back( var == comp );
        }

    }
    return z3::mk_or(equalities);

}

template<typename ID>
z3::expr TranslatorZ3::resolveMaxAssignments(const MaxAssignment <ID> &c, const std::vector<Assignment<ID>*> asgnComb){



}

#endif //OMTSCHED_CONDITIONSZ3_H
