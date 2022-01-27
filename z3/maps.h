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
        SortMap(z3::context &context, const Problem<ID> &problem);

        const z3::sort &getSort(const ID &type) const;

        const z3::expr &getConstant(const ID &) const;

        const ID &getComponent(const z3::expr &) const;

    private:

        void initialize();

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
        initialize();
    };

    template<typename ID>
    void SortMap<ID>::initialize() {


        /*
         * template<typename ID>
    void SortMap<ID>::set(const ID &type, const std::string &name, const std::vector<std::shared_ptr<Component<ID>>> &names, std::vector<z3::func_decl_vector> &enum_consts, std::vector<z3::func_decl_vector> &enum_testers) {

        assert(!names.empty() && "Attempting to create empty sort");

        const char * enum_names[names.size()];
        for(int i = 0; i < names.size(); i++) {
            std::string comp_name = name + "_c" + std::to_string(i);

            enum_names[i] = comp_name.data();

        }

        z3::sort sort = context.enumeration_sort(name.data(), names.size(), enum_names, enum_consts.back(), enum_testers.back());
        sortMap.emplace(type, sort);

        for(int i = 0; i < names.size(); i++) {
            std::string comp_name = name + "_c" + std::to_string(i);
            z3::expr expr = enum_consts.back()[i]();
        }
    }*/
    //template<typename ID>
    //void SortMap<ID>::set(const ID &type, std::vector<std::string> &names) {
        //sortMap.emplace(type, context.uninterpreted_sort(name.c_str()));
        //componentMap.emplace(name, type);
        // "Return an enumeration sort: enum_names[0], ..., enum_names[n-1]. cs and ts are output parameters.
        // The method stores in cs the constants corresponding to the enumerated
        // elements, and in ts the predicates for testing if terms of the enumeration
        // sort correspond to an enumeration."
        //z3::func_decl_vector enum_consts(context);
        //z3::func_decl_vector enum_testers(context);
        //sort s = ctx.enumeration_sort("enumT", 3, enum_names, enum_consts, enum_testers);
        //context.enumeration_sort(name, names.size(), names.data(), enum_consts, enum_testers);
    //}

        int typeCount = 0;

        for(const ID &type : this->problem.getComponentTypes()) {

            std::string name = "s" + std::to_string(typeCount);

            enum_consts.emplace_back(context);
            enum_testers.emplace_back(context);

            //set(const ID &type, const std::string &name, std::vector<z3::func_decl_vector>&, std::vector<z3::func_decl_vector>&);

            //sorts.set(type, name, this->problem.getComponents(type), enum_consts, enum_testers);

            const auto &names = this->problem.getComponents(type);

            // create array needed for enum type
            const char * enum_names[names.size()];
            for(int i = 0; i < names.size(); i++) {
                std::string comp_name = name + "_c" + std::to_string(i);
                enum_names[i] = comp_name.data();
            }

            // make sort
            z3::sort sort = context.enumeration_sort(name.data(), names.size(), enum_names, enum_consts.back(), enum_testers.back());
            sortMap.emplace(type, sort);

            // save components
            size_t i = 0;
            for(const auto &component : names) {
                const ID &id = component->getID();
                std::string comp_name = name + "_c" + std::to_string(i);
                z3::expr expr = enum_consts.back()[i]();
                constantMap.emplace(id, expr);
                i++;
            }

            typeCount++;

        }


    }

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
    struct SlotMap {

    public:
        SlotMap(z3::context &context, const Problem<ID> &problem, const SortMap<ID> &sorts);

        const z3::expr &getVariable(const ID &, const ID &) const;

        const std::pair<ID, ID> &getSlot(const z3::expr &) const;

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

}

#endif //OMTSCHED_MAPS_H
