//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_COMPONENT_H
#define OMTSCHED_COMPONENT_H

template<class ComponentID, class TagID, class GroupID>
class Component {

public:
    Component(const ComponentID &id) : ID{id} {}
    virtual const std::string componentType() const = 0;

private:
    const ComponentID ID;
    std::set<TagID> tags;
    std::set<GroupID> groups;
};

#endif //OMTSCHED_COMPONENT_H
