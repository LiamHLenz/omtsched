//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_RULE_H
#define OMTSCHED_RULE_H


#include "Condition.h"

template<typename ComponentID, typename GroupID, typename TagID>
class Rule {

public:
    bool validate() const;
    void generate(const std::string &path);

    void addAssignments(std::vector<Assignment<ComponentID, GroupID, TagID>*>);
    void removeAssignments(std::vector<Assignment<ComponentID, GroupID, TagID>*>);

private:
    Condition<ComponentID, GroupID, TagID> toplevel;
    bool restrictedSet;
    std::vector<std::vector<Assignment<ComponentID, GroupID, TagID>*>> applicableSets;

};



#endif //OMTSCHED_RULE_H
