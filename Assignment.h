//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_ASSIGNMENT_H
#define OMTSCHED_ASSIGNMENT_H

#include "Component.h"
#include <set>
#include <vector>

class Rule;

struct ComponentSlot {
    const int id;
    const std::string type;
    int number;
    bool optional;
};

template<typename ComponentID, typename GroupID, typename TagID>
class Assignment {

public:
    std::vector<Component<ComponentID, GroupID, TagID>> &getDomain(const int &id);

private:
    std::vector<ComponentSlot> components;
    std::set<Rule> requirements;
};


#endif //OMTSCHED_ASSIGNMENT_H
