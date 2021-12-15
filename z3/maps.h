//
// Created by hal on 13.12.21.
//

#ifndef OMTSCHED_MAPS_H
#define OMTSCHED_MAPS_H

#include <z3.h>
#include <z3++.h>

namespace omtsched {


    /*
    * z3::sort does not define an order so boost::bimap cannot be used directly
    * This is a simple wrapper to circumvent that issue.
    */
    template<typename ID>
    struct SortMap {

    public:
        SortMap(z3::context &context) : context{context} {};
        const z3::sort &getSort(const ID &type) const;
        const ID &getType(const z3::sort &sort) const;
        void set(const ID &type, const std::string &name);
        void remove(const z3::sort &sort);
        void remove(const ID &type);

    private:
        z3::context &context;
        std::map<ID, z3::sort> sortMap;
        std::map<std::string, ID> componentMap;
    };

    template<typename ID>
    const z3::sort &SortMap<ID>::getSort(const ID &type) const {
        return sortMap.at(type);
    }

    template<typename ID>
    const ID &SortMap<ID>::getType(const z3::sort &sort) const {
        return componentMap.at(sort);
    }

    template<typename ID>
    void SortMap<ID>::set(const ID &type, const std::string &name) {
        sortMap.emplace(type, context.uninterpreted_sort(name.c_str()));
        componentMap.emplace(name, type);
    }

    template<typename ID>
    void SortMap<ID>::remove(const z3::sort &sort) {
        const ID &id = componentMap.at(sort);
        sortMap.erase(id);
        componentMap.erase(sort.name().str());
    }

    template<typename ID>
    void SortMap<ID>::remove(const ID &type) {
        const z3::sort &sort = sortMap.at(type);
        sortMap.erase(type);
        componentMap.erase(sort.name().str());
    }


    template<typename ID>
    struct ComponentMap {
    public:
        ComponentMap(z3::context &context) : context{context} {};

        const z3::expr &getVariable(const ID &) const;

        const ID &getComponent(const z3::expr &) const;

        void set(const ID &id, const std::string &varName, const z3::sort &sort, z3::context &context);

        void remove(const ID &);

        void remove(const z3::expr &);

    private:
        z3::context &context;
        std::map<ID, z3::expr> variableMap;
        std::map<std::string, ID> componentMap;
    };

    template<typename ID>
    const z3::expr &ComponentMap<ID>::getVariable(const ID &id) const {
        return variableMap.at(id);
    }

    template<typename ID>
    const ID &ComponentMap<ID>::getComponent(const z3::expr &var) const {
        return componentMap.at(var.get_string());
    }

    template<typename ID>
    void ComponentMap<ID>::set(const ID &id, const std::string &varName, const z3::sort &sort, z3::context &context) {
        variableMap.emplace(std::make_pair(id, context.constant(varName.c_str(), sort)));
        componentMap.emplace(varName, id);
    }

    template<typename ID>
    void ComponentMap<ID>::remove(const ID &id) {
        const z3::expr &var = variableMap.at(id);
        componentMap.erase(var.get_string());
        variableMap.erase(id);
    }

    template<typename ID>
    void ComponentMap<ID>::remove(const z3::expr &var) {
        const ID &id = componentMap.at(var.get_string());
        componentMap.erase(var.get_string());
        variableMap.erase(id);
    }


    template<typename ID>
    struct SlotMap {

    public:
        const z3::expr &getVariable(const ID &, const ID &) const;

        const std::pair<ID, ID> &getSlot(const z3::expr &) const;

        void set(const ID &assignment, const ID &slot, const std::string &name, z3::context &context);

        void remove(const ID &, const ID &);

        void remove(const z3::expr &);

    private:

        // z3::sort does not define an order, so we use 2 unordered maps instead of a bimap
        std::map<std::pair<ID, ID>, z3::expr> variableMap;
        std::map<std::string, std::pair<ID, ID>> slotMap;

    };

    template<typename ID>
    const z3::expr &SlotMap<ID>::getVariable(const ID &assignment, const ID &slot) const {
        return variableMap.at(std::make_pair(assignment, slot));
    }

    template<typename ID>
    const std::pair<ID, ID> &SlotMap<ID>::getSlot(const z3::expr &expr) const {
        return slotMap.at(expr.get_string());
    }

    template<typename ID>
    void SlotMap<ID>::set(const ID &assignment, const ID &slot, const std::string &name, z3::context &context) {

        variableMap.emplace(std::make_pair(std::make_pair(assignment, slot), context.uninterpreted_sort(name.c_str())));
        slotMap.emplace(name, std::make_pair(assignment, slot));
    }

    template<typename ID>
    void SlotMap<ID>::remove(const ID &assignment, const ID &slot) {
        const z3::expr &variable = variableMap.at(std::make_pair(assignment, slot));
        slotMap.erase(variable.get_string());
        variableMap.erase(std::make_pair(assignment, slot));
    }

    template<typename ID>
    void SlotMap<ID>::remove(const z3::expr &expr) {
        const std::pair<ID, ID> &ids = slotMap.at(expr.get_string());
        variableMap.erase(ids);
        slotMap.erase(expr.get_string());
    }

}

#endif //OMTSCHED_MAPS_H
