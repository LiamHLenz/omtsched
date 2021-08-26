//
// Created by dana on 28.04.21.
//

#ifndef OMTSCHED_PROBLEM_H
#define OMTSCHED_PROBLEM_H

#include <set>
#include <vector>
#include "Assignment.h"
#include "Rule.h"
#include "Component.h"

template <typename ComponentID, typename GroupID, typename TagID>
class Problem {

public:

    std::string problemName;

    Problem(const std::string &name);

    // Assignments & components:
    std::vector<Assignments>


    // Groups and Tags

    void addGroup(const GroupID &);

    void deleteGroup(const GroupID &);

    const std::set<GroupID>& getAllGroups() const;


    void addTag(const TagID &id);

    void deleteTag(const TagID &id);

    const std::set<TagID>& getAllTags() const;


private:

    std::set<TagID> tags;

    std::set<GroupID> groups;

    std::vector<Component> components;

    std::vector<Assignment> assignments;

    std::vector<Rule> rules;

    //std::vector<Rule> objectives;

};


#include "Problem.hpp"

#endif //OMTSCHED_PROBLEM_H
