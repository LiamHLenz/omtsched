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

        /*
         * Constructor for a variable component slot
         */
        ComponentSlot(std::string name, ComponentType<ID> componentType, std::size_t number, bool optional) : id{std::move(name)}, type{std::move(componentType)},
        number{number}, optional{optional}, fixed{false} {};

        //TODO: how to use move correctly?
        /*
         * Constructor for a fixed component slot
         */
        ComponentSlot(std::string name, std::vector<Component<ID>> comps) : id{std::move(name)}, type{components.front().getType()},
        number{components.size()}, optional{false}, fixed{true}, components{std::move(components)} {}

        //TODO: fix awkward workaround in ComponentSlot constructor
        ComponentSlot(std::string name, Component<ID> component) : ComponentSlot(name, {}) {components.push_back(component);}

        //ComponentSlot<ID> &operator=(ComponentSlot<ID>&&);

        std::string describe() const;

        const std::string id;
        const ComponentType<ID> type;
        //TODO: either special type or int
        std::size_t number;
        bool optional;

        bool fixed;
        std::vector<Component<ID>> components;
    };

    template<typename ID>
    std::string ComponentSlot<ID>::describe() const {

        std::string s = "";

        std::string sFixed = fixed ? "fixed " : "variable ";
        std::string sOptional = optional ? "optional " : "required ";

        s = sFixed + " component slot " + id + " of type " + type.id + ": ";

        if(fixed)
            for(const auto &comp : components)
                s += " " + comp.getIDString();
        else
            s += std::to_string(number) + " components wanted";

        return s;
    }


    template<typename ID>
    class Assignment {

    public:
        std::vector<Component<ID>> &getDomain(const int &id);
        void setFixed(const std::string &name, Component<ID> component);
        void setVariable(const std::string &name, ID componentType, int number, bool optional);

        const std::map<std::string, ComponentSlot<ID>> & getComponentSlots() const;

    private:
        std::map<std::string, ComponentSlot<ID>> componentSlots;
        //TODO: domains
    
    };


    template<typename ID>
    void Assignment<ID>::setFixed(const std::string &name, const Component<ID> component) {
        componentSlots.emplace(std::make_pair(name, ComponentSlot<std::string>(name, component)));
    }

    template<typename ID>
    void Assignment<ID>::setVariable(const std::string &name, ID componentType, int number, bool optional) {

        componentSlots.emplace(name, {name, componentType, number, optional});
    }

    template<typename ID>
    const std::map<std::string, ComponentSlot<ID>> & Assignment<ID>::getComponentSlots() const {
        return componentSlots;
    }

}

#endif //OMTSCHED_ASSIGNMENT_H
