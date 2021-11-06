//
// Created by dana on 28.04.21.
//

#ifndef OMTSCHED_PROBLEM_H
#define OMTSCHED_PROBLEM_H

#include <set>
#include <vector>
#include <string>
#include <memory>
#include "Assignment.h"
#include "Rule.h"

namespace omtsched {

    template<typename ID>
    class Problem {

    public:

        void print(std::ostream &) const;

        //Component<ID> &newComponent(const ID &id, const ComponentType<ID> &type);

        Component<ID> &newComponent(const ID &id, const ID &type);

        Assignment<ID> &newAssignment(const ID &id);


        const std::set<ID> &getAllGroups() const;

        const std::set<ID> &getAllTags() const;

        const std::vector<Component<ID>> &getComponents(const ID &componentType) const;

        const std::map<ID, Assignment <ID>> &getAssignments() const;

        const std::vector<Rule<ID>> &getRules() const;

        //void addRule(const std::string &);

        //void addRule(const Rule<ID> &&);

        //Rule<ID> &addRule(std::shared_ptr<Condition<ID>> c);
        void addRule(std::shared_ptr<Condition<ID>> c, const bool &hard, const int &weight);

        void addRule(std::shared_ptr<Condition<ID>> c);

        std::vector<ID> getComponentTypes() const;
        const ID addComponentType(const ID &);

        void addGroup(const ID&);

    private:

        std::set<ID> tags;

        std::set<ID> groups;

        std::map<ID, Assignment<ID>> assignments;

        //std::map<ID, Rule<ID>> rules;

        std::vector<Rule<ID>> rules;
        //std::vector<std::pair<Rule<ID>, int>> rulesSoft;

        std::map<ID, std::vector<Component<ID>>> components;

        //std::vector<Rule> objectives;

    };

    template<typename ID>
    void Problem<ID>::addRule(std::shared_ptr<Condition<ID>> c) {

        rules.emplace_back(std::move(c), false, 0);

    }

    template<typename ID>
    void Problem<ID>::addRule(std::shared_ptr<Condition<ID>> c, const bool &optional, const int &weight) {
        rules.emplace_back(std::move(c), optional, weight);
    }
/*
    //itc21.addRule( MaxAssignment( max, InGroup(gameType, mode+team), ComponentIn(slotType, slots)), hard);
    template<typename ID>
    Rule<ID> &Problem<ID>::addRule(std::shared_ptr<Condition<ID>> c, const bool &hard, const int &weight) {

        if(hard)
            return addRule(c);
        else
            return rulesSoft.emplace(std::forward(c), weight).first;
    }
     */

    template<typename ID>
    void Problem<ID>::addGroup(const ID &g) {
        groups.insert(g);
    }

    // Reference can be subject to invalidation, only use locally!
    // TODO: returned iterator can be invalidated in newComponent and newAssignment
    template<typename ID>
    Component<ID> &Problem<ID>::newComponent(const ID &id, const ID &type) {
        return components[type].emplace_back(id);
    }

    // Reference can be subject to invalidation, only use locally!
    template<typename ID>
    Assignment<ID> &Problem<ID>::newAssignment(const ID &id) {
        assignments.emplace(id, id);
        return assignments.at(id);
    }


    template<typename ID>
    std::vector<ID> Problem<ID>::getComponentTypes() const {

        std::vector<ID> types;

        for(const auto &[id, comps] : components)
            types.push_back(id);

        return types;
    }

    template<typename ID>
    const std::vector<Component<ID>> &Problem<ID>::getComponents(const ID &type) const {
        return components.at(type);
    }

    template<typename ID>
    const ID Problem<ID>::addComponentType(const ID &id) {
        components[id]; // create empty vector at position
        return id;
    }

    template<typename ID>
    const std::set<ID> &omtsched::Problem<ID>::getAllGroups() const {
        return groups;
    }

    template<typename ID>
    const std::set<ID> &omtsched::Problem<ID>::getAllTags() const {
        return tags;
    }

    template<typename ID>
    const std::map<ID, Assignment <ID>> &omtsched::Problem<ID>::getAssignments() const {
        return assignments;
    }


    template<typename ID>
    void Problem<ID>::print(std::ostream &ostr) const {

        ostr << "(set-logic QF_EQ)" << std::endl;

        ostr << std::endl;
        ostr << "; Component Types" << std::endl;
        ostr << "; A component types name is t[typeID]" << std::endl;
        ostr << std::endl;

        // Create a sort for each types
        // Format:
        for(const auto &[typeID, components] : components)
            ostr << "(declare-sort " << "t" << typeID << " 0)" << std::endl;

        ostr << std::endl;
        ostr << "; Components" << std::endl;
        ostr << "; a components name is c[componentID]" << std::endl;
        ostr << std::endl;

        for(const auto &[typeID, components] : components){
            for(const Component<ID> &component : components)
                ostr << "(declare-fun c" << component.getID() << " () t" << typeID << ")" << std::endl;
        }


        ostr << std::endl;
        ostr << "; Distinctness Constraints" << std::endl;
        ostr << "; components are assumed to be unique" << std::endl;
        ostr << std::endl;

        for(const auto &[typeID, components] : components){

            ostr << "(distinct";
            for(const Component<ID> &component : components)
                ostr << " c" << component.getID();

            ostr << ")" << std::endl;
        }

        ostr << std::endl;
        ostr << "; Assignments" << std::endl;
        ostr << "; a slot variables name is a[assignmentID]s[slotID]" << std::endl;
        ostr << std::endl;

        // std::map<ID, Assignment<ID>> assignments;
        for(const auto &[asgnID, asgn] : assignments) {
            for(const auto &[slotID, slot] : asgn.getComponentSlots()){

                ostr << "(declare-fun a" << asgnID << "s" << slotID << " () t" << slot.type << ")" << std::endl;

                if(slot.fixed)
                    ostr << "(assert (= a" << asgnID << "s" << slotID <<  " c" << slot.component.getID() << "))" << std::endl;
            }
        }

        // rules specify their own
        for(const auto &rule : rules)
            rule.print(ostr);

        // TODO: optimization

        ostr << "(check-sat)" << std::endl;
    }

}
#endif //OMTSCHED_PROBLEM_H
