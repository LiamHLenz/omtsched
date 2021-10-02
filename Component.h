//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_COMPONENT_H
#define OMTSCHED_COMPONENT_H

#include <map>
#include <set>

template<class ComponentID, class TagID, class GroupID>
class Component {

public:
    Component(const ComponentID &id) : ID{id} {}
    //virtual const std::string componentType() const = 0;

    const ComponentID getId() const;
    const std::map<TagID, int> &getTags() const;
    const std::set<GroupID> &getGroups() const;

    void addGroup(const GroupID&);
    void removeGroup(const GroupID&);

    void setTag(const TagID &, const int);

private:
    const ComponentID ID;
    std::map<TagID, int> tags;
    std::set<GroupID> groups;
};

template<class ComponentID, class TagID, class GroupID>
const ComponentID Component<ComponentID, TagID, GroupID>::getId() const {
    return ID;
}

template<class ComponentID, class TagID, class GroupID>
const std::map<TagID, int> &Component<ComponentID, TagID, GroupID>::getTags() const {
    return tags;
}

template<class ComponentID, class TagID, class GroupID>
const std::set<GroupID> &Component<ComponentID, TagID, GroupID>::getGroups() const {
    return groups;
}

template<class ComponentID, class TagID, class GroupID>
void Component<ComponentID, TagID, GroupID>::addGroup(const GroupID &id) {

    groups.insert(id);
}

template<class ComponentID, class TagID, class GroupID>
void Component<ComponentID, TagID, GroupID>::removeGroup(const GroupID &id) {

    groups.erase(id);
}

template<class ComponentID, class TagID, class GroupID>
void Component<ComponentID, TagID, GroupID>::setTag(const TagID &id, const int val) {

    tags.at(id) = val;
}

#endif //OMTSCHED_COMPONENT_H
