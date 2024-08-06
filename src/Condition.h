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
        MAX_IN_SEQUENCE,
        BLOCKED,
        GREATER, SMALLER, EQUAL

    };

        template<typename ID>
        class Condition {

        public:
            Condition(std::vector<std::shared_ptr<Condition<ID>>> v = {}) : subconditions{v} {}
            virtual const CONDITION_TYPE getType() const = 0;
            virtual void print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const = 0;
            //virtual returnType evaluate(std::vector<std::vector<Assignment<ID>*>>&) = 0;
            virtual void declareVariables(std::ostream &, const std::vector<Assignment<ID>*> &) const;
            std::vector<std::shared_ptr<Condition<ID>>> subconditions = {};

        };



    template<typename ID>
    void Condition<ID>::declareVariables(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const {
        return;
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

    template<typename ID>
    class NamedCondition : public Condition<ID> {

    public:
        NamedCondition(const ID &componentSlot, std::vector<std::shared_ptr<Condition<ID>>> subconditions = {}) : Condition<ID>(subconditions), componentSlot{componentSlot} {}

        const ID getNamedSlot() const;

    protected:
        static int counter;

    private:
        const ID componentSlot;
    };

    template<typename ID>
    const ID NamedCondition<ID>::getNamedSlot() const {
        return componentSlot;
    }

    template<typename ID>
    int NamedCondition<ID>::counter = 0;

}

#endif //OMTSCHED_CONDITION_H
