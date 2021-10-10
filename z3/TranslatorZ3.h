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

namespace omtsched {

    template<typename ID>
    class TranslatorZ3 : public omtsched::Translator<ID> {
    public:
        TranslatorZ3(const Problem <ID> &problem);

        void solve() override;

        z3::context &getContext();

        const z3::expr getVariable(const Assignment<ID> &assignment, const std::string &componentSlot, int num);

        const z3::expr getComponent(const ID &component);

    private:
        void setup();

        void addDomainConstraints(const ComponentSlot &);

        z3::expr resolveCondition(const std::string &r);

        z3::expr resolveVariable(const std::string &r);

        void addRule(const Rule<ID> &);

        int getAssignmentNumber(const Assignment<ID> &assignment);

        Problem<ID> &problem;
        z3::context context;
        z3::solver solver;

        //TODO: double map
        boost::bimap<int, Assignment<ID> *> assignmentOrder;
        boost::bimap<std::string, z3::sort> component_types;
        boost::bimap<ID, z3::expr> components;
        // tuple in order: assignment, slot name, i-th part
        boost::bimap<std::tuple<int, std::string, int>, z3::expr> slots;

    };

    template<typename ID>
    TranslatorZ3<ID>::TranslatorZ3(const Problem <ID> &problem) {

        setup(problem);
    }


    template<typename ID>
    void TranslatorZ3<ID>::setup() {

        // Create sorts for component types
        for (const auto &compType: this->problem.getComponentTypes())
            component_types[compType] = context.uninterpreted_sort(compType);

        // Components
        size_t ccount = 0;
        for (const auto &component: this->problem.getComponents()) {

            // Assign an internal numerical ID
            const auto &type = component_types.right.at(component.getType());
            components[component] = context.constant(ccount, type);
            ccount++;
        }

        // TODO: Components are all distinct



        int a = 0;
        for (const auto &assignment: this->problem.getAssignments()) {
            assignmentOrder[a] = &assignment;
            int c = 0;
            for (const auto &slot: assignment->getSlots()) {
                int i = 0;
                for (const auto &slotPart: slot) {
                    // create assignment variable
                    const auto &type = component_types.right.at(slot.type);
                    std::string name = "a" + std::to_string(a) + "c" + std::to_string(c) + "i" + std::to_string(i);
                    slots[{a, slot.getName(), i}] = context.constant(name, type);
                    i++;
                }
                c++;
            }
            a++;
        }

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
    const z3::expr
    TranslatorZ3<ID>::getVariable(const Assignment<ID> &assignment, const std::string &componentSlot, int num) {

        auto assignmentNumber = getAssignmentNumber(assignment);
        return slots.left.at({assignmentNumber, componentSlot, num});
    }

    template<typename ID>
    const z3::expr TranslatorZ3<ID>::getComponent(const ID &component) {
        return components.at(component);
    }


/*
template<typename ID>
void TranslatorZ3<ID>::domainConstraints() {

    // domain constraint
    z3::expr_vector domain;
    for(const ComponentSlot &c : assignment.getDomain(component))
}


template<typename ID>
z3::expr TranslatorZ3<ID>::resolveVariable(const std::string &r) {


}


template<typename ID>
void TranslatorZ3<ID>::addRule(const Rule &r) {

    z3::expr exp = resolveCondition(r);
    solver.add(exp);

}


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

public:

    bool solve(const Problem<TaskID, TimeslotID, ID, ID> &problem) override;


private:

    //void interpretModelZ3(z3::model, Model &model);
    void outputModelZ3(z3::model);


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


    enum Attributes {
        Start = 0,
        Duration = 1,
        Deadline = 2,
        Optional = 3
    };

};
*/

}

#endif //OMTSCHED_TRANSLATORZ3_H
