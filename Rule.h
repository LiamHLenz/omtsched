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
    void generate(const std::string &path);

    void addAssignments(std::vector<Assignment<ID>*>);
    void removeAssignments(std::vector<Assignment<ID>*>);

private:
    Condition<ID> toplevel;
    bool restrictedSet;
    std::vector<std::vector<Assignment<ID>*>> applicableSets;

};



#endif //OMTSCHED_RULE_H
