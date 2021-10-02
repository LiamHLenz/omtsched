//
// Created by hal on 07.09.21.
//

#ifndef OMTSCHED_CONDITION_H
#define OMTSCHED_CONDITION_H

#include <z3.h>
#include <z3++.h>
#include "ComponentType.h"
#include "Component.h"

template<typename ComponentID, typename TagID, typename GroupID>
class Condition : public ComponentType {

public:
    virtual bool evaluate(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) = 0;

private:
    std::vector<ComponentType> componentTypes;

};



class Not : public Condition {};
z3::expr Not::evaluate(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) {

    return !componentTypes.at(0).evaluate();
}
/*
class And : public Condition {};
z3::expr And::generate(std::vector<Condition> arguments) {

    for()
        inner.generate();

return mk_and();
}

class Or : public Condition {};
z3::expr And::generate(std::vector<Condition> arguments) {

for()
    inner.generate();

return mk_and();
}

class Xor : public Condition {};
z3::expr Xor::generate(std::vector<Condition> arguments) {

for()
generate();

return mk_and();
}

class Implies : public Condition {};
z3::expr Implies::generate(std::vector<Condition> arguments) {

    assert(arguments.size() == 2 && "'Implies' Condition takes exactly two arguments.");
    return z3::implies(generate(arguments.at(0)), generate(arguments.at(1)));
}

class Iff : public Condition {};
z3::expr Iff::generate(std::vector<Condition> arguments) {

    assert(arguments.size() == 2 && "'Iff' Condition takes exactly two arguments.");
    return z3::implies(generate(arguments.at(0)), generate(arguments.at(1)))
        && z3::implies(generate(arguments.at(1)), generate(arguments.at(0)));
}

class NumAssigned 
*/
#endif //OMTSCHED_CONDITION_H
