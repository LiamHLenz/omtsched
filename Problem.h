//
// Created by dana on 28.04.21.
//

#ifndef OMTSCHED_PROBLEM_H
#define OMTSCHED_PROBLEM_H

#include <boost/date_time/posix_time/posix_time.hpp>
#include <map>
#include <set>
#include "Task.h"
#include "Timeslot.h"
#include "Constraint.h"


enum class Unit {
    HOURS,
    MINUTES,
    SECONDS
};

template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
class Problem {

public:

    std::string problemName;

    Problem(const std::string &name, const Unit &unit, const boost::posix_time::ptime &startPoint);

    using Timepoint = boost::posix_time::ptime;
    using Duration = boost::posix_time::time_duration;

    Task<TaskID, GroupID, TagID>& addTask(const TaskID &id, const Timepoint &start, const Duration &duration,
                                          const Timepoint &deadline = boost::date_time::neg_infin, bool optional = false);

    const Task<TaskID, GroupID, TagID>& getTask(const TaskID &id) const;

    const typename std::map<TaskID, Task<TaskID, GroupID, TagID>>& getAllTasks() const;

    bool deleteTask(const TaskID &id);


    Timeslot<TimeslotID, GroupID, TagID>& addTimeslot(const TimeslotID &tsID, const Timepoint &startTime, const Duration &duration);

    const Timeslot<TimeslotID, GroupID, TagID>& getTimeslot(const TimeslotID &id) const;

    const typename std::map<TimeslotID, Timeslot<TimeslotID, GroupID, TagID>>& getAllTimeslots() const;

    bool deleteTimeslot(const TimeslotID &id);


    void addGroup(const GroupID &);

    void deleteGroup(const GroupID &);

    const std::set<GroupID>& getAllGroups() const;


    void addTag(const TagID &id);

    void deleteTag(const TagID &id);

    const std::set<TagID>& getAllTags() const;


    Unit getUnit() const;

    void setUnit(Unit unit);


    const Timepoint &getStartPoint() const;

    void setStartPoint(const Timepoint &startPoint);


    const std::vector<Constraint<TaskID, TimeslotID, GroupID>> &getConstraints() const;


    // Adding constraints

    void bind(const TimeslotID &timeslot, const TaskID& task);

    void oneOf(const std::initializer_list<GroupID>);

    void xOf(const size_t &number, const std::initializer_list<GroupID>);

    void atLeast(const size_t &number, const std::initializer_list<GroupID>);

    void atMost(const size_t &number, const std::initializer_list<GroupID>);

private:

    std::map<TaskID, Task<TaskID, GroupID, TagID>> tasks;

    std::map<TimeslotID, Timeslot<TimeslotID, GroupID, TagID>> timeslots;

    std::set<TagID> tags;

    std::set<GroupID> groups;

    Unit unit;

    Timepoint startPoint;

    std::vector<Constraint<TaskID, TimeslotID, GroupID>> constraints;

};


#include "Problem.hpp"

#endif //OMTSCHED_PROBLEM_H
