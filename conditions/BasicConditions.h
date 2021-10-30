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

        ComponentIs(ID componentSlot, ID component) : componentSlot{componentSlot},
        component{component} {};

        const ID componentSlot;
        const ID component;
    };


    template<typename ID>
    std::shared_ptr<Condition<ID>> componentIs(const ID &slot, const ID &component) {
        return std::make_shared<ComponentIs<ID>>(slot, component);
    }


    template<typename ID>
    class InGroup : public Condition<ID> {

    public:
        InGroup(const ID &componentType, ID groupID) : slot{slot}, group{groupID} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::IN_GROUP;
        const ID slot;
        const ID group;

    };


    template<typename ID>
    class SameComponent : public Condition<ID> {

    public:
        SameComponent(const ID &slotType) : slot{slotType} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::SAME_COMPONENT;
        const ID slot;
    };


    template<typename ID>
    class ComponentIn : public Condition<ID> {

    public:
        ComponentIn(const ID &slotType, std::vector<ID> components) : slotType{slotType}, components{components} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::COMPONENT_IN;
        const ID slotType;
        const std::vector<ID> &components;
    };


}

#endif //OMTSCHED_BASICCONDITIONS_H
