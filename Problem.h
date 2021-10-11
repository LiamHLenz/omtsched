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

    template<typename ID>
    class Problem {

    public:

        const std::string problemName;

        explicit Problem(const std::string &name);

        Component<ID> &newComponent(const ComponentType &type, const ID &id);

        Assignment<ID> &newAssignment();

        std::set<std::string> getComponentTypes() const;


        const std::set<ID> &getAllGroups() const;

        const std::set<ID> &getAllTags() const;

        const std::vector<Component<ID>> &getComponents(const std::string &componentType) const;

        const std::vector<std::unique_ptr<Assignment<ID>>> &getAssignments() const;

        const std::vector<Rule<ID>> &getRules() const;

        void addRule(const std::string &);

        void addRule(const Rule<ID> &);

        //void solve(const bool &allModels);

        void getModel(Model &model) const;

        void printProblem(std::ostream) const;

    private:

        std::set<ID> tags;

        std::set<ID> groups;

        std::vector<Component<ID>> components;

        std::vector<Assignment<ID>> assignments;

        std::vector<Rule<ID>> rules;

        //std::vector<Rule> objectives;

    };

}


template<typename ID>
omtsched::Problem<ID>::
Problem(const std::string &name)
        : problemName(name) {};

template<typename ID>
const std::set<ID> &omtsched::Problem<ID>::getAllGroups() const {

    return groups;
}

template<typename ID>
const std::set<ID> &omtsched::Problem<ID>::getAllTags() const {
    return tags;
}

template<typename ID>
const std::vector<std::unique_ptr<Component<ID>>> &
omtsched::Problem<ID>::getComponents() const {
    return components;
}

template<typename ID>
const std::vector<std::unique_ptr<Assignment<ID>>> &omtsched::Problem<ID>::getAssignments() const {
    return assignments;
}

template<typename ID>
const std::vector<Rule<ID>> &omtsched::Problem<ID>::getRules() const {
    return rules;
}

template<typename ID>
void omtsched::Problem<ID>::addRule(const std::string &) {


}

template<typename ID>
void omtsched::Problem<ID>::addRule(const Rule<ID> &) {


}


#endif //OMTSCHED_PROBLEM_H
