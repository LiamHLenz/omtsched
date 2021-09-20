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
#include "encoding/Rule.h"
#include "Component.h"

namespace omtsched {

    template<typename ComponentID, typename GroupID, typename TagID>
    class Problem {

    public:

        std::string problemName;

        explicit Problem(const std::string &name);

        Problem();


        Component<ComponentID, GroupID, TagID> &addComponent(const ComponentID &);

        Assignment &addAssignment();

        std::set<std::string> getComponentTypes() const;


        // Groups and Tags

        void addGroup(const GroupID &);

        void deleteGroup(const GroupID &);

        const std::set<GroupID> &getAllGroups() const;


        void addTag(const TagID &id);

        void deleteTag(const TagID &id);

        const std::set<TagID> &getAllTags() const;


        const std::vector<std::unique_ptr<Component<ComponentID, GroupID, TagID>>> &getComponents() const;

        const std::vector<std::unique_ptr<Assignment>> &getAssignments() const;

        const std::vector<Rule> &getRules() const;


    private:

        std::set<TagID> tags;

        std::set<GroupID> groups;

        std::vector<std::unique_ptr<Component<ComponentID, GroupID, TagID>>> components;

        std::vector<std::unique_ptr<Assignment>> assignments;

        std::vector<Rule> rules;

        //std::vector<Rule> objectives;

    };

}

#include "Problem.hpp"

#endif //OMTSCHED_PROBLEM_H
