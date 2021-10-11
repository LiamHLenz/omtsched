//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_ASSIGNMENT_H
#define OMTSCHED_ASSIGNMENT_H

#include "Component.h"
#include <vector>

template<typename ID>
struct ComponentSlot {
    const std::string id;
    const ID type;
    int number;
    bool optional;
};

template<typename ID>
class Assignment {

public:
    std::vector<Component<ID>> &getDomain(const int &id);

private:
    std::vector<ComponentSlot> componentSlots;
    //TODO: domains
    
};


#endif //OMTSCHED_ASSIGNMENT_H
