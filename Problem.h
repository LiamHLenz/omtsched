//
// Created by dana on 28.04.21.
//

#ifndef OMTSCHED_PROBLEM_H
#define OMTSCHED_PROBLEM_H

#include <set>

template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
class Problem {

public:

    std::string problemName;

    Problem(const std::string &name);

    // Assignments & components:


    // Groups and Tags

    void addGroup(const GroupID &);

    void deleteGroup(const GroupID &);

    const std::set<GroupID>& getAllGroups() const;


    void addTag(const TagID &id);

    void deleteTag(const TagID &id);

    const std::set<TagID>& getAllTags() const;


    Unit getUnit() const;

    void setUnit(Unit unit);


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
