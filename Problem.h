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
#include "Component.h"
#include "Model.h"

namespace omtsched {

    template<typename ComponentID, typename GroupID, typename TagID>
    class Problem {

    public:

        const std::string problemName;

        explicit Problem(const std::string &name);

        Component<ComponentID, GroupID, TagID> &newComponent(const ComponentType &type, const ComponentID &id);

        Assignment<ComponentID, GroupID, TagID> &newAssignment();

        std::set<std::string> getComponentTypes() const;


        const std::set<GroupID> &getAllGroups() const;

        const std::set<TagID> &getAllTags() const;


        const std::vector<std::unique_ptr<Component<ComponentID, GroupID, TagID>>> &getComponents() const;

        const std::vector<std::unique_ptr<Assignment<ComponentID, GroupID, TagID>>> &getAssignments() const;

        const std::vector<Rule<ComponentID, GroupID, TagID>> &getRules() const;

        void addRule(const std::string &);

        void addRule(const Rule<ComponentID, GroupID, TagID> &);

        //void solve(const bool &allModels);

        void getModel(Model &model) const;

        void printProblem(std::ostream) const;

    private:

        std::set<TagID> tags;

        std::set<GroupID> groups;

        std::vector<std::unique_ptr<Component<ComponentID, GroupID, TagID>>> components;

        std::vector<std::unique_ptr<Assignment<ComponentID, GroupID, TagID>>> assignments;

        std::vector<Rule<ComponentID, GroupID, TagID>> rules;

        //std::vector<Rule> objectives;

    };

}


template<typename ComponentID, typename GroupID, typename TagID>
omtsched::Problem<ComponentID, GroupID, TagID>::
Problem(const std::string &name)
        : problemName(name) {};

template<typename ComponentID, typename GroupID, typename TagID>
const std::set<GroupID> &omtsched::Problem<ComponentID, GroupID, TagID>::getAllGroups() const {

    return groups;
}

template<typename ComponentID, typename GroupID, typename TagID>
const std::set<TagID> &omtsched::Problem<ComponentID, GroupID, TagID>::getAllTags() const {
    return tags;
}

template<typename ComponentID, typename GroupID, typename TagID>
const std::vector<std::unique_ptr<Component<ComponentID, GroupID, TagID>>> &
omtsched::Problem<ComponentID, GroupID, TagID>::getComponents() const {
    return components;
}

template<typename ComponentID, typename GroupID, typename TagID>
const std::vector<std::unique_ptr<Assignment<ComponentID, GroupID, TagID>>> &omtsched::Problem<ComponentID, GroupID, TagID>::getAssignments() const {
    return assignments;
}

template<typename ComponentID, typename GroupID, typename TagID>
const std::vector<Rule<ComponentID, GroupID, TagID>> &omtsched::Problem<ComponentID, GroupID, TagID>::getRules() const {
    return rules;
}

template<typename ComponentID, typename GroupID, typename TagID>
void omtsched::Problem<ComponentID, GroupID, TagID>::addRule(const std::string &) {


}

template<typename ComponentID, typename GroupID, typename TagID>
void omtsched::Problem<ComponentID, GroupID, TagID>::addRule(const Rule<ComponentID, GroupID, TagID> &) {


}

template<typename ComponentID, typename GroupID, typename TagID>
void omtsched::Problem<ComponentID, GroupID, TagID>::getModel(Model &model) const {


    // Preprocessing steps:
    // 1. Determine free variables

    // 2. Determine variable domains

    // 3. Determine for every rule the set of applicable parameters and simplify

    // 4. Determine which resulting rules are domain restrictions and apply them

    // 5. Determine types used

    // Translation steps:
    // 1. Create assignment variables with constrained domains

    // 2. Instantiate rules


    // Re-translate model steps:
    // 1.
}

#endif //OMTSCHED_PROBLEM_H
