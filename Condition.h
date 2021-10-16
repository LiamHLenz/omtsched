//
// Created by hal on 07.09.21.
//

#ifndef OMTSCHED_CONDITION_H
#define OMTSCHED_CONDITION_H


#include "ComponentType.h"
#include "Component.h"

namespace omtsched {

    enum class CONDITION_TYPE {

        NOT, OR, AND, XOR, IMPLIES, IFF,
        COMPONENT_IS,
        MAX_ASSIGNMENTS

    };

    template<typename ID>
    class Condition {

    public:
        Condition() : Condition({}) {};
        Condition(std::initializer_list<Condition<ID>> sc);
        //virtual bool evaluate(std::vector<Component<ID>*>& arguments) = 0;
        //virtual bool validParameters(std::vector<Component<ID>*>& arguments) = 0;

    protected:
        // specifies the types of
        ID conditionID;
        std::vector<ComponentType<ID>> paramenterTypes;
        std::vector<Condition<ID>> subconditions;

    };

    template<typename ID>
    Condition<ID>::Condition(std::initializer_list<Condition<ID>> sc) : subconditions{sc} {}

}

#endif //OMTSCHED_CONDITION_H
