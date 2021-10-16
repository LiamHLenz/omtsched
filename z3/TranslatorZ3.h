//
// Created by dana on 11.05.21.
//

#ifndef OMTSCHED_TRANSLATORZ3_H
#define OMTSCHED_TRANSLATORZ3_H


#include "../Translator.h"
#include <z3.h>
#include <z3++.h>
#include <map>
#include <boost/bimap.hpp>


template<> struct std::hash<z3::sort> {
    std::size_t operator()(const z3::sort & sort) const noexcept {
        return sort.hash();
    }
};


namespace omtsched {

    /*
    * z3::sort does not define an order so boost::bimap cannot be used directly
    * This is a simple wrapper to circumvent that issue.
    */
    template<typename ID>
    struct sortMap {

    public:
        z3::sort getSort(const ID &) const;
        ID getType(const z3::sort &) const;

        void set(const ID &, const z3::sort &);
        void remove(const ID &);
        void remove(const z3::sort &);

    private:

        // z3::sort does not define an order, so we use 2 unordered maps instead of a bimap
        std::unordered_map<ID, z3::sort> componentTypeSorts;
        std::unordered_map<z3::sort, ID> componentTypeNames;

    };

    template<typename ID>
    z3::sort sortMap<ID>::getSort(const ID &id) const {
        return componentTypeSorts.at(id);
    }

    template<typename ID>
    ID sortMap<ID>::getType(const z3::sort &sort) const {
        return componentTypeNames.at(sort);
    }

    template<typename ID>
    void sortMap<ID>::set(const ID &id, const z3::sort &sort) {
        //TODO: any type of error checking anywhere
        componentTypeNames[id] = sort;
        componentTypeSorts[sort] = id;
    }

    template<typename ID>
    void sortMap<ID>::remove(const ID &id) {
        const auto &sort = componentTypeSorts.at(id);
        componentTypeNames.erase(sort);
        componentTypeSorts.erase(id);
    }

    template<typename ID>
    void sortMap<ID>::remove(const z3::sort &sort) {
        const auto &id = componentTypeNames.at(sort);
        componentTypeNames.erase(sort);
        componentTypeSorts.erase(id);
    }

    template <typename ID>
    class TranslatorZ3 : public omtsched::Translator<ID> {
    public:
        TranslatorZ3(const Problem<ID> &problem);
        void solve() override;
        Model getModel() override;

        z3::context &getContext();
        const z3::expr getVariable(const Assignment<ID> &assignment, const std::string &componentSlot, int num);
        const z3::expr getComponent(const ID &component);

    private:
        void setupVariables();
        void addRule(const Rule<ID> &);

        int getAssignmentNumber(const Assignment<ID> &assignment);

        z3::context context;
        z3::solver solver;

        //TODO: double map
        boost::bimap<int, Assignment<ID>*> assignmentOrder;

        sortMap<ID> sortMap;
        boost::bimap<ID, z3::expr> components;
        // tuple in order: assignment, slot name, i-th part
        boost::bimap<std::tuple<int, std::string, int>, z3::expr> slots;

    };

    template<typename ID>
    TranslatorZ3<ID>::TranslatorZ3(const Problem<ID> &problem) {

        setup(problem);
    }

    template<typename ID>
    int TranslatorZ3<ID>::getAssignmentNumber(const Assignment<ID> &assignment) {

        return assignmentOrder.at(assignment);
    }

    template<typename ID>
    z3::context &TranslatorZ3<ID>::getContext() {
        return context;
    }

    template<typename ID>
    const z3::expr TranslatorZ3<ID>::getVariable(const Assignment<ID> &assignment, const std::string &componentSlot, int num) {

        auto assignmentNumber = getAssignmentNumber(assignment);
        return slots.left.at({assignmentNumber, componentSlot, num});
    }

    template<typename ID>
    const z3::expr TranslatorZ3<ID>::getComponent(const ID &component){
        return components.at(component);
    }

    template<typename ID>
    void TranslatorZ3<ID>::setupVariables() {
        //TODO: make this not like this

        // Create component types and components
        for (const auto &compType: this->problem.getComponentTypes()) {
            const ID &typeID = compType.getID();
            sortMap.set(typeID, context.uninterpreted_sort(compType));
            // Components
            size_t ccount = 0;
            z3::expr_vector comps {context};
            for (const auto &component: this->problem.getComponents(compType)) {

                // Assign an internal numerical ID
                const z3::sort &type = sortMap.get(typeID);
                const std::string name = "c" + std::to_string(ccount);
                components[component] = context.constant(name.c_str(), type);
                ccount++;
                comps.push_back(components.at(component));
            }
            // Components are assumed to be unique
            addRule(z3::distinct(comps));
        }

        // Create Assignments
        int a = 0;
        for(const auto &assignment : this->problem.getAssignments()) {
            assignmentOrder[a] = &assignment;
            int c = 0;
            for (const auto &slot: assignment->getSlots()) {
                int i = 0;
                for(const auto &component : slot.components){
                    // create assignment variable
                    const auto &type = sortMap.get(component.getType());
                    std::string name = "a"+std::to_string(a)+"c"+std::to_string(c)+"i"+std::to_string(i);
                    slots[{a, slot.getName(), i}] = context.constant(name.c_str(), type);
                    i++;
                }
                c++;
            }
            a++;
        }

        solver = z3::solver{context};

    }


    template<typename ID>
    void TranslatorZ3<ID>::solve() {

        const auto result = solver.check();

        if(result == z3::unsat)
            std::cout << "UNSAT" << std::endl;

        else if(result == z3::sat) {

            std::cout << "SAT" << std::endl;
            z3::model m = solver.get_model();
        }

        else if(result == z3::unknown)
            std::cout << "UNKNOWN" << std::endl;


    }

    template<typename ID>
    void TranslatorZ3<ID>::addRule(const Rule<ID> &rule) {

        // recursively resolve constraints

    }

    /*
     * z3::expr_vector z3args {};
        for(const auto s : subconditions)
            z3args.push_back(s.instantiate(assignmentGroups));

        return z3::mk_or(z3args);
     */

    /*
     * z3::expr Iff::generate(std::vector<Condition> arguments) {

        assert(arguments.size() == 2 && "'Iff' Condition takes exactly two arguments.");
        return z3::implies(generate(arguments.at(0)), generate(arguments.at(1)))
            && z3::implies(generate(arguments.at(1)), generate(arguments.at(0)));
    }
     */

    /*
     * template<typename ID>
    z3::expr Not<ID>::instantiate(std::vector<Component < ID, ID, ID>*>& arguments) {

        return !arguments.at(0).evaluate();
    }
     */

    /*
     *   template<typename ID>
    z3::expr And<ID>::instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) {

        z3::expr_vector z3args;
        for(const auto s : subconditions)
            z3args.push_back(s.instantiate(assignmentGroups));

        return z3::mk_and(z3args);
    }
    */

    /*
     *  template<typename ID>
    z3::expr
    ComponentIs<ID>::instantiate(const Translator<ID> &t, const std::vector<const std::vector<const Assignment<ID> *>> &assignmentGroups) {

        //If there is more than one assignment: conjunction
        z3::expr_vector equalities (t.getContext());
        for(const auto &assignment : assignmentGroups) {
            const z3::expr &var = t.getVariable(assignment, componentSlot);
            const z3::expr &component = t.getComponent(component);
            equalities.push_back(var == component);
        }

        return z3::mk_and(equalities);

    }

     */

    /*
     * z3::expr MaxAssignment<ID>::instantiate(const std::vector<const std::vector< const Assignment<ID>*>>& assignmentGroups) {

    /*
     * Resolved by:
     * 1. creating a bitvector of (relevant) assignments
     * 2. creating an implication for each assignment: if the conditions are met the
     *    bit corresponding to the assignment is set
     * 3. constraining the maximum number of set bits
     /

    //
}
     */


    //-----------
    /*

    template <typename Key1, typename Key2>
    class expr_map {

    public:
        const z3::expr get(const Key1 &key1, const Key2 &key2) const;
        void set(const Key1 &key1, const Key2 &key2, z3::expr expr);

    private:
        std::map<std::pair<Key1, Key2>, std::vector<z3::expr>> internal_map;

    };


    template <typename TaskID, typename TimeslotID, typename ID, typename ID>
    class TranslatorZ3 : public Translator<TaskID, TimeslotID, ID, ID> {

        /*
        const std::string assigned(const size_t &tid, const size_t &aid) const;

        const char* makeID(const std::string &type, const size_t &number, const std::string &attribute) const;
        const char* makeID(const std::string &type, const size_t &num1, const std::string &attribute, const size_t &num2) const;

        int timeInUnit(const Unit &unit, const boost::posix_time::time_duration &duration) const;
        int timeBetween(const Unit &unit, const boost::posix_time::ptime &first, const boost::posix_time::ptime &second) const;

        // ----------------------------------
        std::map<TaskID, size_t> task_id;
        std::map<TimeslotID, size_t> ts_id;
        std::map<ID, size_t> tag_id;
        std::map<ID, size_t> group_id; */

    //-- datastructures for Z3 ----------
    /*
        // This should work better
        std::map<TaskID, std::vector<z3::expr>> task_expr;
        std::map<TimeslotID, std::vector<z3::expr>> ts_expr;

        // These are tricky, since z3 has no default constructor, which is needed by map
        // Implementation subject to change, hence encapsulation in own class
        expr_map<TimeslotID, ID> assign_expr;

        expr_map<TaskID, ID> task_tags;
        expr_map<TaskID, ID> task_groups;
        expr_map<TimeslotID, ID> ts_tags;
        expr_map<TimeslotID, ID> ts_groups;


    };
    */

}

#endif //OMTSCHED_TRANSLATORZ3_H
