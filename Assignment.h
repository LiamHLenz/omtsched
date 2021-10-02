//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_ASSIGNMENT_H
#define OMTSCHED_ASSIGNMENT_H

#include "Component.h"
#include <vector>

struct ComponentSlot {
    const int id;
    const int type;
    int number;
    bool optional;
};

template<typename ComponentID, typename GroupID, typename TagID>
class Assignment {

public:
    std::vector<Component<ComponentID, GroupID, TagID>> &getDomain(const int &id);

private:
    std::vector<ComponentSlot> componentSlots;
    //TODO: domains
    
};


#endif //OMTSCHED_ASSIGNMENT_H
