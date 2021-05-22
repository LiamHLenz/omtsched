//
// Created by dana on 19.05.21.
//

#ifndef OMTSCHED_CONSTRAINT_H
#define OMTSCHED_CONSTRAINT_H

#include <vector>

enum class ConstraintType {

    BIND,
    X_OF,
    AT_LEAST,
    AT_MOST

};

template <typename TaskID, typename TimeslotID, typename GroupID>
class Constraint {

public:

    Constraint(const ConstraintType &type, const size_t &num, const std::initializer_list<GroupID> &groups);
    Constraint(const ConstraintType &type, const TimeslotID &ts, const TaskID &task);

    const ConstraintType type;
    const size_t number;
    std::set<GroupID> groups;
    const TaskID task;
    const TimeslotID ts;

};

template <typename TaskID, typename TimeslotID, typename GroupID>
Constraint<TaskID, TimeslotID, GroupID>::Constraint(const ConstraintType &type, const size_t &num, const std::initializer_list<GroupID> &groups)
: type{type}, number{num}, groups{groups} {}

template <typename TaskID, typename TimeslotID, typename GroupID>
Constraint<TaskID, TimeslotID, GroupID>::Constraint(const ConstraintType &type, const TimeslotID &ts, const TaskID &task)
: type{type}, ts{ts}, task{task} {}

#endif //OMTSCHED_CONSTRAINT_H
