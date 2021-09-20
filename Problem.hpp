//
// Created by dana on 28.04.21.
//


#include "Problem.h"

template<typename ComponentID, typename GroupID, typename TagID>
omtsched::Problem<ComponentID, GroupID, TagID>::
Problem(const std::string &name)
    : problemName(name) {};

template<typename ComponentID, typename GroupID, typename TagID>
omtsched::Problem<ComponentID, GroupID, TagID>::
Problem() {};

template<typename ComponentID, typename GroupID, typename TagID>
void omtsched::Problem<ComponentID, GroupID, TagID>::addGroup(const GroupID &id) {

    groups.insert(id);
}

template<typename ComponentID, typename GroupID, typename TagID>
void omtsched::Problem<ComponentID, GroupID, TagID>::deleteGroup(const GroupID &id) {

    for(auto &component : components)
        component->removeGroup(id);

    groups.erase(id);
}

template<typename ComponentID, typename GroupID, typename TagID>
const std::set<GroupID> &omtsched::Problem<ComponentID, GroupID, TagID>::getAllGroups() const {

    return groups;
}

template<typename ComponentID, typename GroupID, typename TagID>
void omtsched::Problem<ComponentID, GroupID, TagID>::addTag(const TagID &id) {

    for(auto &component : components)
        component->addTag(id);

    tags.insert(id);

}

template<typename ComponentID, typename GroupID, typename TagID>
void omtsched::Problem<ComponentID, GroupID, TagID>::deleteTag(const TagID &id) {

    for(auto &component : components)
        component->removeTag(id);

    tags.erase(id);
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
const std::vector<std::unique_ptr<Assignment>> &omtsched::Problem<ComponentID, GroupID, TagID>::getAssignments() const {
    return assignments;
}

template<typename ComponentID, typename GroupID, typename TagID>
const std::vector<Rule> &omtsched::Problem<ComponentID, GroupID, TagID>::getRules() const {
    return rules;
}
