//
// Created by hal on 07.09.21.
//

#ifndef OMTSCHED_CONDITION_H
#define OMTSCHED_CONDITION_H


#include "ComponentType.h"
#include "Component.h"

namespace omtsched {

    enum class CONDITION_TYPE {

        BASE,
        NOT, OR, AND, XOR, IMPLIES, IFF,
        COMPONENT_IS, COMPONENT_IN, SAME_COMPONENT, DISTINCT,
        IN_GROUP,
        MAX_ASSIGNMENTS, MIN_ASSIGNMENTS,
        MAX_IN_SEQUENCE

    };

        template<typename ID>
        class Condition {

        public:
            const CONDITION_TYPE getType();
            virtual void print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const = 0;
            //virtual returnType evaluate(std::vector<std::vector<Assignment<ID>*>>&) = 0;

        protected:
            CONDITION_TYPE conditionType = CONDITION_TYPE::BASE;

        };

        template<typename ID>
        const CONDITION_TYPE Condition<ID>::getType() {
            return conditionType;
        }

        /*
        template<typename ID, typename returnType>
        class CompositeCondition : public Condition<ID, returnType> {

        public:
            const CONDITION_TYPE getType();
            //virtual returnType evaluate(std::vector<std::vector<Component<ID>*>>& arguments) = 0;
            //virtual bool validParameters(std::vector<Component<ID>*>& arguments) = 0;

        protected:
            std::vector<std::shared_ptr<Condition<ID, returnType>>> subconditions;

        };
        */


}

#endif //OMTSCHED_CONDITION_H
