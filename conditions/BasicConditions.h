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
        static const CONDITION_TYPE type = CONDITION_TYPE::COMPONENT_IS;

        ComponentIs(std::string, ID);
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
    class MaxAssignment : public Condition<ID> {

    public:
        MaxAssignment(std::initializer_list<Condition<ID>> sc, const int &max);
        const int max;

    };

    template<typename ID>
    MaxAssignment<ID>::MaxAssignment(std::initializer_list<Condition <ID>> sc, const int &max) : max{ max }, Condition<ID>{sc} {}
}

#endif //OMTSCHED_BASICCONDITIONS_H
