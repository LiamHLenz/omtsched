//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_ASSIGNMENT_H
#define OMTSCHED_ASSIGNMENT_H

#include "Component.h"
#include "ComponentType.h"
#include <utility>
#include <vector>

namespace omtsched {

    // special values
    enum Number {
        ONE_OR_MORE = -1,
        ANY = -2
    };

    template<typename ID>
    struct ComponentSlot {

        ComponentSlot() = default;

        /*
         * Constructor for a variable component slot
         */
        ComponentSlot(ID componentType, bool optional = false, bool fixed = false) : type{componentType}, optional{optional}, fixed{fixed} {};

        /*
         * Constructor for a fixed component slot
         */
        ComponentSlot(Component<ID> &&comp) : type{comp.getType()},
         optional{false}, fixed{true}, component{comp.getID()} {}

        ComponentSlot<ID> &operator=(ComponentSlot<ID>&&);

        void addComponent(const Component<ID>&);

        std::string describe() const;

        const ID type;
        bool optional;

        bool fixed;
        ID component;
    };

    template<typename ID>
    void ComponentSlot<ID>::addComponent(const Component<ID> &c) {
        component = c.getID();
    }

    template<typename ID>
    ComponentSlot<ID> &ComponentSlot<ID>::operator=(ComponentSlot<ID> &&cs) {

        if (&cs == this)
            return *this;

        type = cs.type;
        optional = cs.optional;
        fixed = cs.fixed;
        component = std::move(cs);

        return *this;
    }

    /*
    template<typename ID>
    std::string ComponentSlot<ID>::describe() const {

        std::string s = "";

        std::string sFixed = fixed ? "fixed " : "variable ";
        std::string sOptional = optional ? "optional " : "required ";

        s = sFixed + " component slot of type " + type + ": ";

        if(fixed)
            s += std::to_string(number) + " components.";
            //for(const auto &comp : components)
                //s += " " + comp; // TODO
        else
            s += std::to_string(number) + " components wanted.";

        return s;
    }
*/


    template<typename ID>
    class Assignment {

    public:
        Assignment(const ID &id) : id{id}, optional{false}, weight{0} {}

        void setFixed(const ID &name, const Component<ID>&);
        void setFixed(const ID &name, std::vector<Component<ID>>&);

        void setVariable(const ID &name, ID componentType, bool optional);

        const std::map<ID, ComponentSlot<ID>> & getComponentSlots() const;
        
        const ComponentSlot<ID> &getSlot(const ID &) const;

        void setOptional(bool optional);

        void setWeight(int weight);

        int getWeight() const;

        const ID getID() const;

        bool isOptional() const;

    private:
        std::map<ID, ComponentSlot<ID>> componentSlots;
        bool optional;
        int weight;
        const ID id;
        };

    template<typename ID>
    void Assignment<ID>::setFixed(const ID &name, const Component<ID> &comps) {

        componentSlots.emplace(std::piecewise_construct, std::make_tuple(name), std::make_tuple(comps));
    }

    template<typename ID>
    void Assignment<ID>::setVariable(const ID &name, ID componentType, bool optional) {

        componentSlots.emplace(std::piecewise_construct, std::make_tuple(name), std::make_tuple(componentType, optional));
    }

    template<typename ID>
    const std::map<ID, ComponentSlot<ID>> & Assignment<ID>::getComponentSlots() const {
        return componentSlots;
    }

    template<typename ID>
    void Assignment<ID>::setOptional(bool optional) {
        Assignment::optional = optional;
    }

    template<typename ID>
    void Assignment<ID>::setWeight(int weight) {
        Assignment::weight = weight;
    }

    template<typename ID>
    const ID Assignment<ID>::getID() const {
        return id;
    }

    template<typename ID>
    bool Assignment<ID>::isOptional() const {
        return optional;
    }

    template<typename ID>
    int Assignment<ID>::getWeight() const {
        return weight;
    }

    template<typename ID>
    const ComponentSlot<ID> &Assignment<ID>::getSlot(const ID &id) const {
        return componentSlots.at(id);
    }



}

#endif //OMTSCHED_ASSIGNMENT_H
