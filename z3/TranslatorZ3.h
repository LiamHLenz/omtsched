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

template <typename ID>
class TranslatorZ3 : public omtsched::Translator<ID> {
public:
    TranslatorZ3(const Problem<ID> &problem);
    void solve() override;
    Model getModel() override;

    z3::context getContext();
    const z3::expr getVariable(const Assignment<ID> &assignment, const std::string &componentSlot, int num);
    const z3::expr getComponent(const ID &component);

private:
    void setup();
    void addDomainConstraints(const ComponentSlot &);
    z3::expr resolveCondition(const std::string &r);
    z3::expr resolveVariable(const std::string &r);
    void addRule(const Rule &);

    int getAssignmentNumber(const Assignment<ID> &assignment);

    z3::context context;
    z3::solver solver;

    //TODO: double map
    boost::bimap<int, Assignment<ID>*> assignmentOrder;
    boost::bimap<std::string, z3::sort> component_types;
    boost::bimap<ID, z3::expr> components;
    // tuple in order: assignment, slot name, i-th part
    boost::bimap<std::tuple<int, std::string, int>, z3::expr> slots;

};

template<typename ID>
TranslatorZ3<ID>::TranslatorZ3(const Problem<ID> &problem) {

    setup(problem);
}


int TranslatorZ3<ID>::getAssignmentNumber(const Assignment<ID> &assignment) {

    return assignmentOrder.at(assignment);
}

template<typename ID>
z3::context TranslatorZ3<ID>::getContext(){
    return context;
}

template<typename ID>
const z3::expr TranslatorZ3<ID>::getVariable(const Assignment<ID> &assignment, const std::string &componentSlot, int num) {

    auto assignmentNumber = getAssignmentNumber(assignment);
    return slots.at({assignmentNum, componentSlot, num});
}

template<typename ID>
const z3::expr TranslatorZ3<ID>::getComponent(const ID &component){
    return components.at(component);
}

template<typename ID>
void TranslatorZ3<ID>::setup(problem) {

    // Create component types and components
    for (const auto &compType: this->problem.getComponentTypes()) {
        component_types[compType] = context.uninterpreted_sort(compType);
        // Components
        size_t ccount = 0;
        z3::expr_vector comps {context};
        for (const auto &component: this->problem.getComponents(compType)) {

            // Assign an internal numerical ID
            const auto &type = component_types.at(component.getType());
            components[component] = context.constant(ccount, type);
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
            for(const auto &slotPart : slot){
                // create assignment variable
                const auto &type = component_types.at(component.getType());
                std::string name = "a"+std::to_string(a)+"c"+std::to_string(c)+"i"+std::to_string(i);
                slotVars[{a, slot.getName(), i}] = context.constant(name, type);
                i++;
            }
            c++;
        }
        a++;
    }

    solver = z3::solver{context};

    // Add Rules
    for(const Rule &rule : problem.getRules())
        solver.add(rule.generate());

}


template<typename ID>
void TranslatorZ3<ID>::solve() {

    switch(solver.check()){

        case z3::unsat:
            std::cout << "UNSAT" << std::endl;
            break;

        case z3::sat:
            std::cout << "SAT" << std::endl;
            z3::model m = solver.get_model();
            break;

        case z3::unknown:
            std::cout << "UNKNOWN" << std::endl;
            break;
    }

}

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

#endif //OMTSCHED_TRANSLATORZ3_H
