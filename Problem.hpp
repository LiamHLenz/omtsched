//
// Created by dana on 28.04.21.
//


#include "Problem.h"

template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
Problem<TaskID, TimeslotID, GroupID, TagID>::
Problem(const std::string &name, const Unit &unit, const boost::posix_time::ptime &startPoint)
    : problemName(name), unit(unit), startPoint(startPoint) {};

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
Task<TaskID, GroupID, TagID>& Problem<TaskID, TimeslotID, GroupID, TagID>::addTask(
        const TaskID &id, const Timepoint &start, const Duration &duration,
        const Timepoint &deadline, bool optional) {

    auto res = tasks.insert( std::pair(id, Task<TaskID, GroupID, TagID> {id, start, duration, deadline, optional}) );

    // Todo: Error handling
    // Case: Key already exists
    //if(!res.second)

    Task<TaskID, GroupID, TagID>& task = res.first->second;

    // Add all tags (at normal priority 1)
    for(auto &tag : tags)
        task.addTag(tag);

    return task;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const Task<TaskID, GroupID, TagID>& Problem<TaskID, TimeslotID, GroupID, TagID>::getTask(const TaskID &id) const {

    return tasks.at(id);
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const typename std::map<TaskID, Task<TaskID, GroupID, TagID>>& Problem<TaskID, TimeslotID, GroupID, TagID>::getAllTasks() const {

    return tasks;

}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
bool Problem<TaskID, TimeslotID, GroupID, TagID>::deleteTask(const TaskID &id) {

    if(!tasks.count(id))
        return false;

    tasks.erase(id);
    return true;

}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
Timeslot<TimeslotID, GroupID, TagID> &Problem<TaskID, TimeslotID, GroupID, TagID>::addTimeslot(const TimeslotID &tsID, const Timepoint &startTime, const Duration &duration) {

    auto res = timeslots.insert( std::pair(tsID, Timeslot <TimeslotID, GroupID, TagID> {tsID, startTime, duration}) );

    // Case: Key already existed
    //if(!res.second)

    Timeslot <TimeslotID, GroupID, TagID> &ts = res.first->second;



    // Add all tags (at normal priority 1)
    for(auto &tag : tags)
        ts.addTag(tag);

    return ts;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const Timeslot<TimeslotID, GroupID, TagID> &Problem<TaskID, TimeslotID, GroupID, TagID>::getTimeslot(const TimeslotID &id) const {
    return timeslots.at(id);
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const typename std::map<TimeslotID, Timeslot<TimeslotID, GroupID, TagID>>&
Problem<TaskID, TimeslotID, GroupID, TagID>::getAllTimeslots() const {

    return timeslots;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
bool Problem<TaskID, TimeslotID, GroupID, TagID>::deleteTimeslot(const TimeslotID &id) {
    return false;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::addGroup(const GroupID &id) {

    groups.insert(id);
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::deleteGroup(const GroupID &id) {

    for(auto &pair : tasks)
        pair.second.removeGroup(id);

    for(auto &pair : timeslots)
        pair.second.removeGroup(id);

    groups.erase(id);
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const std::set<GroupID> &Problem<TaskID, TimeslotID, GroupID, TagID>::getAllGroups() const {

    return groups;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::addTag(const TagID &id) {

    for(auto &pair : tasks)
        pair.second.addTag(id);

    for(auto &pair : timeslots)
        pair.second.addTag(id);

    tags.insert(id);

}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::deleteTag(const TagID &id) {

    //if(!tasks.count(id))

    for(auto &task : tasks)
        task.second.removeTag(id);

    for(auto &pair : timeslots)
        pair.second.removeTag(id);

    tags.erase(id);
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const std::set<TagID> &Problem<TaskID, TimeslotID, GroupID, TagID>::getAllTags() const {
    return tags;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::bind(const TimeslotID &ts, const TaskID &task) {



}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
Unit Problem<TaskID, TimeslotID, GroupID, TagID>::getUnit() const {
    return unit;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::setUnit(Unit unit) {
    Problem::unit = unit;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const typename Problem<TaskID, TimeslotID, GroupID, TagID>::Timepoint &Problem<TaskID, TimeslotID, GroupID, TagID>::getStartPoint() const {
    return startPoint;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::setStartPoint(const Problem::Timepoint &startPoint) {
    Problem::startPoint = startPoint;
}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::oneOf(const std::initializer_list<GroupID>) {

}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::xOf(const size_t &number, const std::initializer_list<GroupID>) {

}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::atLeast(const size_t &number, const std::initializer_list<GroupID>) {

}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Problem<TaskID, TimeslotID, GroupID, TagID>::atMost(const size_t &number, const std::initializer_list<GroupID>) {

}
