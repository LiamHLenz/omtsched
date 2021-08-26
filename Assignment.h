//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_ASSIGNMENT_H
#define OMTSCHED_ASSIGNMENT_H

#include "Component.h"
#include <set>
#include <vector>

class Rule;

class Assignment {

public:
    virtual std::set<Variable> generate() const;

private:
    std::vector<std::shared_ptr<Component>> components;
    std::set<Rule> requirements;
};


#endif //OMTSCHED_ASSIGNMENT_H
