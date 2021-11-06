//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_RULE_H
#define OMTSCHED_RULE_H


#include "Condition.h"
#include <iostream>

namespace omtsched {
    template<typename ID>
    class Rule {

    public:
        Rule(std::shared_ptr<Condition<ID>> condition) : toplevel{std::move(condition)} {}
        Rule(std::shared_ptr<Condition<ID>> condition, const bool &optional, const int &weight) : toplevel{std::move(condition)}, optional{optional}, weight{weight} {}

        Rule(const Rule<ID>& r);

        Rule<ID>& operator=(Rule<ID>&& r);

        //Rule(const Rule &);
        //bool validate() const;

        //void addAssignments(std::vector<Assignment<ID>*>);
        //void removeAssignments(std::vector<Assignment<ID>*>);

        const Condition<ID> &getTopCondition() const;

        const std::vector<std::vector<Assignment<ID> *>> &getApplicableSets() const;

        bool isRestricted() const;

        void print(std::ostream &) const;

    private:
        std::shared_ptr<Condition<ID>> toplevel;
        bool restrictedSet;
        std::vector<std::vector<Assignment<ID>*>> applicableSets;
        bool optional;
        int weight;
    };

    template<typename ID>
    Rule<ID>::Rule(const Rule<ID>& r) {

        toplevel = r.toplevel;
        optional = r.optional;
        weight = r.weight;
        restrictedSet = r.restrictedSet;
        applicableSets = r.applicableSets;
    }

    template<typename ID>
    Rule<ID> &Rule<ID>::operator=(Rule<ID> &&r){

        if (&r == this)
            return *this;

        toplevel = std::move(r.toplevel);
        optional = r.optional;
        weight = r.weight;
        restrictedSet = r.restrictedSet;
        applicableSets = r.applicableSets;

        return *this;
    }

    template<typename ID>
    bool Rule<ID>::isRestricted() const {
        return restrictedSet;
    }

    template<typename ID>
    const std::vector<std::vector<Assignment<ID> *>> &Rule<ID>::getApplicableSets() const {
        return applicableSets;
    }

    //template<typename ID>
    //void Rule<ID>::addAssignments(std::vector<Assignment<ID>*> assignments) {
    //    applicableSets.push_back(assignments);
    //}

    //TODO: the complication is finding different permutations
    // of the same set
    //template<typename ID>
    //void Rule<ID>::removeAssignments(std::vector<Assignment<ID>*>);

    /*
    template<typename ID>
    z3::expr Rule<ID>::generate() {

        // A rule needs to be instantiated for every combination of assignments

    }*/

    template<typename ID>
    void Rule<ID>::print(std::ostream &ostr) const {

        if(optional){ // TODO: optionality
            }

        // TODO: restricted sets

        ostr << "(assert ";

        // generate condition for each combination of assignments
        for(const std::vector<Assignment<ID>*> &asgns : applicableSets)
            toplevel->print(ostr, asgns);

        ostr << ")" << std::endl;
    }

}

#endif //OMTSCHED_RULE_H
