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

template <typename ComponentID, typename GroupID, typename TagID>
class TranslatorZ3 : public omtsched::Translator<ComponentID, GroupID, TagID> {
public:
    TranslatorZ3();
    void solve() override;

private:
    void setup();
    void addDomainConstraints(const ComponentSlot &);
    z3::expr resolveCondition(const std::string &r);
    z3::expr resolveVariable(const std::string &r);
    void addRule(const Rule &);

    z3::context context;
    z3::solver solver;

    //TODO: double map
    std::vector<Assignment<ComponentID, GroupID, TagID>*> assignmentOrder;
    boost::bimap<std::string, z3::sort> component_types;
    boost::bimap<ComponentID, z3::expr> components;
    // tuple in order: assignment, slot name, i-th part
    boost::bimap<std::tuple<int, std::string, int>, z3::expr> slots;

};

template<typename ComponentID, typename GroupID, typename TagID>
TranslatorZ3<ComponentID, GroupID, TagID>::TranslatorZ3() {}

template<typename ComponentID, typename GroupID, typename TagID>
void TranslatorZ3<ComponentID, GroupID, TagID>::solve() {

}

template<typename ComponentID, typename GroupID, typename TagID>
void TranslatorZ3<ComponentID, GroupID, TagID>::setup() {

    // Create sorts for component types
    for (const auto &compType: this->problem.getComponentTypes())
        component_types[compType] = context.uninterpreted_sort(compType);

    // Components
    size_t ccount = 0;
    for (const auto &component: this->problem.getComponents()) {

        // Assign an internal numerical ID
        const auto &type = component_types.at(component.getType());
        components[component] = context.constant(ccount, type);
        ccount++;
    }

    // Components are all distinct



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
}
/*
template<typename ComponentID, typename GroupID, typename TagID>
void TranslatorZ3<ComponentID, GroupID, TagID>::domainConstraints() {

    // domain constraint
    z3::expr_vector domain;
    for(const ComponentSlot &c : assignment.getDomain(component))
}


template<typename ComponentID, typename GroupID, typename TagID>
z3::expr TranslatorZ3<ComponentID, GroupID, TagID>::resolveVariable(const std::string &r) {


}


template<typename ComponentID, typename GroupID, typename TagID>
void TranslatorZ3<ComponentID, GroupID, TagID>::addRule(const Rule &r) {

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


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
class TranslatorZ3 : public Translator<TaskID, TimeslotID, GroupID, TagID> {

public:

    bool solve(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem) override;


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
    std::map<TagID, size_t> tag_id;
    std::map<GroupID, size_t> group_id; */

    //-- datastructures for Z3 ----------
/*
    // This should work better
    std::map<TaskID, std::vector<z3::expr>> task_expr;
    std::map<TimeslotID, std::vector<z3::expr>> ts_expr;

    // These are tricky, since z3 has no default constructor, which is needed by map
    // Implementation subject to change, hence encapsulation in own class
    expr_map<TimeslotID, TagID> assign_expr;

    expr_map<TaskID, TagID> task_tags;
    expr_map<TaskID, GroupID> task_groups;
    expr_map<TimeslotID, TagID> ts_tags;
    expr_map<TimeslotID, GroupID> ts_groups;


    enum Attributes {
        Start = 0,
        Duration = 1,
        Deadline = 2,
        Optional = 3
    };

};
*/

#endif //OMTSCHED_TRANSLATORZ3_H
