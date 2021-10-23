//
// Created by Betrieb-PC on 06.10.2021.
//

#ifndef OMTSCHED_BOOLEANCONDITIONS_H
#define OMTSCHED_BOOLEANCONDITIONS_H

#include "../Condition.h"

namespace omtsched {


    template<typename ID>
    class Not : public Condition<ID> {

    public:
        Not(Condition<ID> subcondition) : subcondition{std::move(subcondition)} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::NOT;
        const Condition<ID> subcondition;
    };


    template<typename ID>
    class And : public Condition<ID> {

        public:
            And(std::vector<Condition<ID>> subconditions) : subconditions{std::move(subconditions)} {}
            static const CONDITION_TYPE type = CONDITION_TYPE::AND;
            const std::vector<Condition<ID>> subconditions;
        };


    template<typename ID>
    class Or : public Condition<ID> {

    public:
        Or(std::vector<Condition<ID>> subconditions) : subconditions{std::move(subconditions)} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::OR;
        const std::vector<Condition<ID>> subconditions;
    };


    template<typename ID>
    class Implies : public Condition<ID> {
    public:
        Implies(Condition<ID> antecedent, Condition<ID> consequent) : antecedent{std::move(antecedent)}, consequent{std::move(consequent)} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::IMPLIES;
        const Condition<ID> antecedent;
        const Condition<ID> consequent;
    };

    template<typename ID>
    class Xor : public Condition<ID> {
    public:
        Xor(Condition<ID> first, Condition<ID> second) : first{std::move(first)}, second{std::move(second)} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::XOR;
        const Condition<ID> first;
        const Condition<ID> second;
    };

    template<typename ID>
    class Iff : public Condition<ID> {
    public:
        Iff(Condition<ID> first, Condition<ID> second) : first{std::move(first)}, second{std::move(second)} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::IFF;
        const Condition<ID> first;
        const Condition<ID> second;
    };

}
#endif //OMTSCHED_BOOLEANCONDITIONS_H
