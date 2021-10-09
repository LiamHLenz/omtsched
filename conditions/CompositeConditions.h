//
// Created by Betrieb-PC on 06.10.2021.
//

#ifndef OMTSCHED_COMPOSITECONDITIONS_H
#define OMTSCHED_COMPOSITECONDITIONS_H

#include "../Condition.h"

//  ------------
//      Not

template<typename ComponentID, typename TagID, typename GroupID>
class Not : public Condition<ComponentID, TagID, GroupID> {

public:
    Not(const std::vector<Condition<ComponentID, TagID, GroupID>*> subconditions);
    virtual z3::expr instantiate(std::vector<Component < ComponentID, TagID, GroupID>*>& arguments) override;
    virtual bool validParameters(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) override;
};

template<typename ComponentID, typename TagID, typename GroupID>
z3::expr Not<ComponentID, TagID, GroupID>::instantiate(std::vector<Component < ComponentID, TagID, GroupID>*>& arguments) {

    return !arguments.at(0).evaluate();
}

//  ------------
//      And

template<typename ComponentID, typename TagID, typename GroupID>
class And : public Condition<ComponentID, TagID, GroupID> {

    public:
        And(const std::vector<Condition<ComponentID, TagID, GroupID>*> subconditions);
        virtual bool evaluate(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) override;
        virtual bool validParameters(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) override;
        virtual z3::expr instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) = 0;
    };

template<typename ComponentID, typename TagID, typename GroupID>
z3::expr And<ComponentID, TagID, GroupID>::instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) {

    z3::expr_vector z3args;
    for(const auto s : subconditions)
        z3args.push_back(s.instantiate(assignmentGroups));

    return z3::mk_and(z3args);
}

//  ------------
//      Not

template<typename ComponentID, typename TagID, typename GroupID>
class Or : public Condition<ComponentID, TagID, GroupID> {

    public:
        Or(const Condition ... subconditions);
        virtual bool evaluate(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) override;
        virtual bool validParameters(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) override;
    };

template<typename ComponentID, typename TagID, typename GroupID>
z3::expr Or<ComponentID, TagID, GroupID>::instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) {

    z3::expr_vector z3args;
    for(const auto s : subconditions)
        z3args.push_back(s.instantiate(assignmentGroups));

    return z3::mk_or(z3args);
}


//  ------------
//    Implies

template<typename ComponentID, typename TagID, typename GroupID>
class Implies : public Condition<ComponentID, TagID, GroupID> {

    public:
        Implies(const std::vector<Condition<ComponentID, TagID, GroupID>*> subconditions);
        virtual bool evaluate(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) override;
        virtual bool validParameters(std::vector<Component<ComponentID, TagID, GroupID>*>& arguments) override;
    };

template<typename ComponentID, typename TagID, typename GroupID>
z3::expr Implies<ComponentID, TagID, GroupID>::instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) {

    return z3::implies(subconditions.at(0).evaluate(assignmentGroups), subconditions.at(1).evaluate(assignmentGroups));
}

/*
class Xor : public Condition {};
z3::expr Xor::generate(std::vector<Condition> arguments) {

for()
generate();

return mk_and();
}

class Iff : public Condition {};
z3::expr Iff::generate(std::vector<Condition> arguments) {

    assert(arguments.size() == 2 && "'Iff' Condition takes exactly two arguments.");
    return z3::implies(generate(arguments.at(0)), generate(arguments.at(1)))
        && z3::implies(generate(arguments.at(1)), generate(arguments.at(0)));
}
*/

#endif //OMTSCHED_COMPOSITECONDITIONS_H
