//
// Created by hal on 13.12.21.
//

#ifndef OMTSCHED_MAPS_H
#define OMTSCHED_MAPS_H

#include <z3.h>
#include <z3++.h>
#include <cstring>

namespace omtsched {

    /*
    * z3::sort does not define an order so boost::bimap cannot be used directly
    * This is a simple wrapper to circumvent that issue.
    */
    template<typename ID>
    struct SortMap {

    public:
        SortMap(z3::context &context, const Problem<ID> &problem);

        const z3::sort &getSort(const ID &type) const;

        const z3::expr &getConstant(const ID &) const;

        const ID &getComponent(const z3::expr &) const;

        void print() const;

    private:

        const Problem<ID> &problem;
        z3::context &context;

        std::map<ID, z3::sort> sortMap;

        std::map<ID, z3::expr> constantMap;
        std::map<unsigned, ID> componentMap;

        std::vector<z3::func_decl_vector> enum_consts;
        std::vector<z3::func_decl_vector> enum_testers;

    };

    template<typename ID>
    SortMap<ID>::SortMap(z3::context &context, const Problem<ID> &problem) : context{context}, problem{problem} {

        int typeCount = 0;

        for(const ID &type : this->problem.getComponentTypes()) {

            std::string name = "s" + std::to_string(typeCount);

            enum_consts.emplace_back(context);
            enum_testers.emplace_back(context);

            const auto &names = this->problem.getComponents(type);

            // create array needed for enum type
            char * enum_names [names.size()];
            for(int i = 0; i < names.size(); i++) {

                std::string comp_name = name + "_c" + std::to_string(i);
                enum_names[i] = new char;
                std::strcpy(enum_names[i], comp_name.data());

            }

            // make sort
            z3::sort sort = context.enumeration_sort(name.data(), names.size(), enum_names, enum_consts.back(), enum_testers.back());
            sortMap.emplace(type, sort);

            for(char * pointer : enum_names)
                delete pointer;

            // save components
            size_t i = 0;
            for(const auto &component : names) {
                const ID &id = component->getID();
                z3::expr expr = enum_consts.back()[i]();
                constantMap.emplace(id, expr);
                componentMap.emplace(expr.id(), id);
                i++;
            }

            typeCount++;

        }
    };

    template<typename ID>
    const z3::sort &SortMap<ID>::getSort(const ID &type) const {
        return sortMap.at(type);
    }

    template<typename ID>
    const z3::expr &SortMap<ID>::getConstant(const ID &id) const {
        return constantMap.at(id);
    }

    template<typename ID>
    const ID &SortMap<ID>::getComponent(const z3::expr &expr) const {
        return componentMap.at(expr.id());
    }

    template<typename ID>
    void SortMap<ID>::print() const {

        std::cout << std::endl << "START SORT MAP TEST PRINT" << std::endl << std::endl;

        std::cout << "Sorts: " <<   std::endl;

        for(const auto &[id, sort] : sortMap)
            std::cout << "ID: " << id << " Value: " << sort <<   std::endl;

        std::cout << std::endl << "Constants:" <<   std::endl;

        for(const auto &[id, expr] : constantMap)
            std::cout << "ID: " << id << " Value: " << expr <<   std::endl;

        std::cout << std::endl << "ComponentMap:" << std::endl;
        // std::map<unsigned, ID> componentMap;

        for(const auto &[uns, id] : componentMap)
            std::cout << "Unsigned: " << uns << " ID: " << id <<   std::endl;

        std::cout << std::endl << "END SORT MAP TEST PRINT" << std::endl << std::endl;

    }


    template<typename ID>
    struct SlotMap {

    public:
        SlotMap(z3::context &context, const Problem<ID> &problem, const SortMap<ID> &sorts);

        const z3::expr &getVariable(const ID &, const ID &) const;

        const std::pair<ID, ID> &getSlot(const z3::expr &) const;

        void print() const;

    private:
        std::map<std::pair<ID, ID>, z3::expr> variableMap;
        std::map<std::string, std::pair<ID, ID>> slotMap;

    };

    template<typename ID>
    SlotMap<ID>::SlotMap(z3::context &context, const Problem<ID> &problem, const SortMap<ID> &sorts) {

        int a = 0;
        for (const auto &[aid, assignment] : problem.getAssignments()) {
            int c = 0;
            for (const auto &[sid, slot] : assignment.getComponentSlots()) {
                // create assignment variable
                const z3::sort &type = sorts.getSort(slot.type);
                const std::string &name = "a" + std::to_string(a) + "c" + sid;
                variableMap.emplace(std::make_pair(assignment.getID(), sid), context.constant(name.c_str(), type));
                slotMap.emplace(name, std::make_pair(assignment.getID(), sid));
                c++;
            }
            a++;
        }
    }

    template<typename ID>
    const z3::expr &SlotMap<ID>::getVariable(const ID &assignment, const ID &slot) const {
        return variableMap.at(std::make_pair(assignment, slot));
    }

    template<typename ID>
    const std::pair<ID, ID> &SlotMap<ID>::getSlot(const z3::expr &expr) const {
        return slotMap.at(expr.get_string());
    }

    template<typename ID>
    void SlotMap<ID>::print() const {

        // std::map<std::pair<ID, ID>, z3::expr> variableMap;
        // std::map<std::string, std::pair<ID, ID>> slotMap;

        std::cout << std::endl << "START SLOT MAP TEST PRINT" << std::endl << std::endl;

        std::cout << "VariableMap: " <<   std::endl;

        for(const auto &[pair, expr] : variableMap)
            std::cout << "ID: " << pair.first << ", " << pair.second << " Value: " << expr << std::endl;

        std::cout << std::endl << "Slots:" <<   std::endl;

        for(const auto &[name, pair] : slotMap)
            std::cout << "Value: " << name << ", Slot: " << pair.first << ", " << pair.second << std::endl;

        std::cout << std::endl << "END SLOT MAP TEST PRINT" << std::endl << std::endl;


    }

}

#endif //OMTSCHED_MAPS_H
