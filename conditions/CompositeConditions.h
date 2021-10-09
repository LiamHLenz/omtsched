//
// Created by Betrieb-PC on 06.10.2021.
//

#ifndef OMTSCHED_COMPOSITECONDITIONS_H
#define OMTSCHED_COMPOSITECONDITIONS_H

#include "../Condition.h"

//  ------------
//      Not

template<typename ID, typename ID, typename ID>
class Not : public Condition<ID> {

public:
    Not(const std::vector<Condition<ID>*> subconditions);
    virtual z3::expr instantiate(std::vector<Component < ID, ID, ID>*>& arguments) override;
    virtual bool validParameters(std::vector<Component<ID>*>& arguments) override;
};

template<typename ID, typename ID, typename ID>
z3::expr Not<ID>::instantiate(std::vector<Component < ID, ID, ID>*>& arguments) {

    return !arguments.at(0).evaluate();
}

//  ------------
//      And

template<typename ID, typename ID, typename ID>
class And : public Condition<ID> {

    public:
        And(const std::vector<Condition<ID>*> subconditions);
        virtual bool evaluate(std::vector<Component<ID>*>& arguments) override;
        virtual bool validParameters(std::vector<Component<ID>*>& arguments) override;
        virtual z3::expr instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) = 0;
    };

template<typename ID, typename ID, typename ID>
z3::expr And<ID>::instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) {

    z3::expr_vector z3args;
    for(const auto s : subconditions)
        z3args.push_back(s.instantiate(assignmentGroups));

    return z3::mk_and(z3args);
}

//  ------------
//      Not

template<typename ID, typename ID, typename ID>
class Or : public Condition<ID> {

    public:
        Or(const Condition ... subconditions);
        virtual bool evaluate(std::vector<Component<ID>*>& arguments) override;
        virtual bool validParameters(std::vector<Component<ID>*>& arguments) override;
    };

template<typename ID, typename ID, typename ID>
z3::expr Or<ID>::instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) {

    z3::expr_vector z3args;
    for(const auto s : subconditions)
        z3args.push_back(s.instantiate(assignmentGroups));

    return z3::mk_or(z3args);
}


//  ------------
//    Implies

template<typename ID, typename ID, typename ID>
class Implies : public Condition<ID> {

    public:
        Implies(const std::vector<Condition<ID>*> subconditions);
        virtual bool evaluate(std::vector<Component<ID>*>& arguments) override;
        virtual bool validParameters(std::vector<Component<ID>*>& arguments) override;
    };

template<typename ID, typename ID, typename ID>
z3::expr Implies<ID>::instantiate(const std::vector<const std::vector< const Assignment*>>& assignmentGroups) {

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
