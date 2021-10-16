//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_RULE_H
#define OMTSCHED_RULE_H


#include "Condition.h"

namespace omtsched {
    template<typename ID>
    class Rule {

    public:
        Rule(const Condition<ID> &condition);
        Rule(const Rule &);
        bool validate() const;

        void addAssignments(std::vector<Assignment<ID>*>);
        void removeAssignments(std::vector<Assignment<ID>*>);

        std::string to_string() const;

    private:
        std::unique_ptr<Condition<ID>> toplevel;
        bool restrictedSet;
        std::vector<std::vector<Assignment<ID>*>> applicableSets;

    };

    template<typename ID>
    Rule<ID>::Rule(const Condition<ID> &condition) : toplevel{std::make_unique<Condition<ID>>(condition)} {}

    template<typename ID>
    Rule<ID>::Rule(const Rule &r) : toplevel{r.toplevel}, restrictedSet{r.restrictedSet}, applicableSets{r.applicableSets} {}

    template<typename ID>
    void Rule<ID>::addAssignments(std::vector<Assignment<ID>*> assignments) {
        applicableSets.push_back(assignments);
    }

    //TODO: the complication is finding different permutations
    // of the same set
    //template<typename ID>
    //void Rule<ID>::removeAssignments(std::vector<Assignment<ID>*>);

    /*
    template<typename ID>
    z3::expr Rule<ID>::generate() {

        // A rule needs to be instantiated for every combination of assignments

    }*/

}

#endif //OMTSCHED_RULE_H
