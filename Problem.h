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

        Component<ID> &newComponent(const ID &id, const ComponentType<ID> &type);

        Assignment<ID> &newAssignment();

        void addComponentType(const ID &id);

        std::set<ID> getComponentTypes() const;


        const std::set<ID> &getAllGroups() const;

        const std::set<ID> &getAllTags() const;

        const std::vector<Component<ID>> &getComponents(const std::string &componentType) const;

        const std::vector<Assignment<ID>> &getAssignments() const;

        const std::vector<Rule<ID>> &getRules() const;

        void addRule(const std::string &);

        void addRule(const Rule<ID> &);


    private:

        std::set<ID> tags;

        std::set<ID> groups;

        std::vector<Component<ID>> components;

        std::vector<Assignment<ID>> assignments;

        std::vector<Rule<ID>> rules;

        std::set<ID> componentTypes;

        //std::vector<Rule> objectives;

    };

    // Reference can be subject to invalidation, only use locally!
    // TODO: returned reference can be invalidated in newComponent and newAssignment
    template<typename ID>
    Component<ID> &Problem<ID>::newComponent(const ID &id, const ComponentType<ID> &type) {
        auto it = components.template emplace_back(id, type);
        return it;
    }

    // Reference can be subject to invalidation, only use locally!
    template<typename ID>
    Assignment<ID> &Problem<ID>::newAssignment() {
        auto it = assignments.emplace_back();
        return it;
    }

    template<typename ID>
    void Problem<ID>::addComponentType(const ID &id) {
        componentTypes.template emplace({id});
    }

    template<typename ID>
    std::set<ID> Problem<ID>::getComponentTypes() const {
        return componentTypes;
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
    const std::vector<Component<ID>> &omtsched::Problem<ID>::getComponents(const std::string &componentType) const {
        return components;
    }

    template<typename ID>
    const std::vector<Assignment<ID>> &omtsched::Problem<ID>::getAssignments() const {
        return assignments;
    }

    template<typename ID>
    const std::vector<Rule<ID>> &omtsched::Problem<ID>::getRules() const {
        return rules;
    }


    template<typename ID>
    void omtsched::Problem<ID>::addRule(const Rule<ID> &rule) {
        rules.push_back(rule);
    }

}
#endif //OMTSCHED_PROBLEM_H
