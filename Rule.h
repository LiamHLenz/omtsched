//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_RULE_H
#define OMTSCHED_RULE_H


#include "Condition.h"

template<typename ID>
class Rule {

public:
    bool validate() const;
    z3::expr generate();

    void addAssignments(std::vector<Assignment<ID>*>);
    void removeAssignments(std::vector<Assignment<ID>*>);

private:
    Condition<ID> toplevel;
    bool restrictedSet;
    std::vector<std::vector<Assignment<ID>*>> applicableSets;

};

template<typename ID>
void Rule<ID>::addAssignments(std::vector<Assignment<ID>*> assignments) {
    applicableSets.push_back(assignments);
}

//TODO: the complication is finding different permutations
// of the same set
//template<typename ID>
//void Rule<ID>::removeAssignments(std::vector<Assignment<ID>*>);

template<typename ID>
z3::expr Rule<ID>::generate() {

    // A rule needs to be instantiated for every combination of assignments

}



#endif //OMTSCHED_RULE_H
