//
// Created by Betrieb-PC on 07.10.2021.
//

#ifndef OMTSCHED_BASICCONDITIONS_H
#define OMTSCHED_BASICCONDITIONS_H

#include "../Condition.h"

namespace omtsched {

    template<typename ID>
    class ComponentIs : public Condition<ID> {

    public:
        ComponentIs(std::string, ID);

        z3::expr instantiate(const Translator<ID> &t, const std::vector<const std::vector<const Assignment<ID> *>> &assignmentGroups);
        //virtual bool evaluate(std::vector<Component<ID>*>& arguments) = 0;
        //virtual bool validParameters(std::vector<Component<ID>*>& arguments) = 0;

    private:
        const std::string componentSlot;
        const ID component;
    };

    template<typename ID>
    ComponentIs<ID>::ComponentIs(std::string componentSlot, ID component) : componentSlot{componentSlot},
                                                                            component{component} {}

    template<typename ID>
    z3::expr
    ComponentIs<ID>::instantiate(const Translator<ID> &t, const std::vector<const std::vector<const Assignment<ID> *>> &assignmentGroups) {

        //If there is more than one assignment: conjunction
        z3::expr_vector equalities (t.getContext());
        for(const auto &assignment : assignmentGroups) {
            const z3::expr &var = t.getVariable(assignment, componentSlot);
            const z3::expr &component = t.getComponent(component);
            equalities.push_back(var == component);
        }

        return z3::mk_and(equalities);

    }

}

#endif //OMTSCHED_BASICCONDITIONS_H
