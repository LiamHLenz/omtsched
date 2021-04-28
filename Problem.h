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


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
class Problem {

public:

    using Timepoint = boost::posix_time::ptime;
    using Duration = boost::posix_time::time_duration;

    Task<TaskID, GroupID, TagID>& addTask(const TaskID &id, const Timepoint &start, const Duration &duration,
                                          const Timepoint &deadline = boost::date_time::neg_infin, bool optional = false);

    Task<TaskID, GroupID, TagID>& getTask(const TaskID &id);

    typename std::map<TaskID, Task<TaskID, GroupID, TagID>>::iterator getAllTasks() const;

    bool deleteTask(const TaskID &id);


    Timeslot<TimeslotID, GroupID, TagID>& addTimeslot(const TimeslotID &tsID, const Timepoint &startTime, const Duration &duration);

    Timeslot<TimeslotID, GroupID, TagID>& getTimeslot(const TimeslotID &id);

    typename std::map<TimeslotID, Timeslot<TimeslotID, GroupID, TagID>>::iterator getAllTimeslots() const;

    bool deleteTimeslot(const TimeslotID &id);


    void addGroup(const GroupID &);

    void deleteGroup(const GroupID &);

    const std::set<GroupID>& getAllGroups() const;


    void addTag(const TagID &id);

    void deleteTag(const TagID &id);

    const std::set<TagID>& getAllTags() const;

private:

    std::map<TaskID, Task<TaskID, GroupID, TagID>> tasks;

    std::map<TimeslotID, Timeslot<TimeslotID, GroupID, TagID>> timeslots;

    std::set<TagID> tags;

    std::set<GroupID> groups;

};


#include "Problem.hpp"

#endif //OMTSCHED_PROBLEM_H
