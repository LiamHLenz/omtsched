//
// Created by dana on 26.04.21.
//

#ifndef OMTSCHED_TASK_H
#define OMTSCHED_TASK_H

#include <boost/date_time.hpp>
#include <set>
#include <map>
#include "../Component.h"

namespace omtsched {



}

/*
template<typename ID>
class Task {

public:

    // Abbreviating long typenames, mainly to keep constructor arguments readable
    using Timepoint = boost::posix_time::ptime;
    using Duration = boost::posix_time::time_duration;

    /**
     *
     * @param id IDs can be of any type, the only requirement is that they need to be unique
     * @param start The first time point at which the task can be scheduled.
     * @param duration The estimated duration of the task. Tasks will only be scheduled for timeslots
     *        equal to or longer than this.
     * @param deadline The cut-off point after which the task cannot be scheduled.
     * @param optional Every non-optional task must be scheduled before its deadline for a schedule
     *        to be considered valid.
     */
/*
    Task(const ID &id, const Timepoint &start, const Duration &duration,
            const Timepoint &deadline = boost::date_time::neg_infin, bool optional = false);

    /**
     * Tasks can belong to groups, being of the same type or belonging to a collection
     * of some form. They exist to create constraints and optimality criteria
     * and help find patterns of failure.
     * @param group ID of the group to add. The group needs to be registered using addGroup() before.
     */
/*
    bool addGroup(const ID &group);

    bool removeGroup(const ID &group);

    bool inGroup(const ID &group) const;

    [[nodiscard]] const std::set<ID> &getGroups() const;

    bool setTagPriority(const ID &tag, const unsigned int &priority);

    [[nodiscard]] const int getTagPriority(const ID &tag) const;

    [[nodiscard]] const ID getTaskId() const;

    [[nodiscard]] const Timepoint &getStartPoint() const;

    void setStartPoint(const Timepoint &startPoint);

    [[nodiscard]] const Timepoint &getDeadline() const;

    void setDeadline(const Timepoint &deadline);

    [[nodiscard]] const Duration &getDuration() const;

    void setDuration(const Duration &duration);

    [[nodiscard]] bool isOptional() const;

    void setOptional(const bool &optional);

    void addTag(const ID &ID);

    void removeTag(const ID &ID);

private:

    const ID taskID;
    Timepoint startPoint;
    Timepoint deadline;
    Duration duration;
    std::set<ID> groups;
    std::map<ID, unsigned int> tags;
    bool optional;

};


template <typename ID, typename ID, typename ID>
Task<ID>::Task(const ID &id, const Task::Timepoint &start, const Task::Duration &duration,
                               const Task::Timepoint &deadline, bool optional)
        : taskID{id}, startPoint{start}, duration{duration}, deadline{deadline}, optional{optional} {

    // for(auto &ID : getAllTags())
    //    tags[ID] = 1;
}


template<typename ID>
bool Task<ID>::addGroup(const ID &group) {

    //if(!allGroups().count())
    //  return false;

    groups.insert(group);
    return true;

}

template<typename ID>
bool Task<ID>::removeGroup(const ID &group) {

    groups.erase(group);
}

template<typename ID>
bool Task<ID>::setTagPriority(const ID &tag, const unsigned  int &priority) {

    if(!tags.count(tag))
        return false;

    tags.at(tag) = priority;

    return true;
}

template<typename ID>
const int Task<ID>::getTagPriority(const ID &tag) const {

    if(!tags.count(tag))
        return -1;

    return tags.at(tag);
}

template<typename ID>
const ID Task<ID>::getTaskId() const {
    return taskID;
}

template<typename ID>
const boost::posix_time::ptime &Task<ID>::getStartPoint() const {
    return startPoint;
}

template<typename ID>
void Task<ID>::setStartPoint(const Task::Timepoint &startPoint) {
    Task::startPoint = startPoint;
}

template<typename ID>
const boost::posix_time::ptime &Task<ID>::getDeadline() const {
    return deadline;
}

template<typename ID>
void Task<ID>::setDeadline(const Task::Timepoint &deadline) {
    Task::deadline = deadline;
}

template<typename ID>
const boost::posix_time::time_duration &Task<ID>::getDuration() const {
    return duration;
}

template<typename ID>
void Task<ID>::setDuration(const Task::Duration &duration) {
    Task::duration = duration;
}

template<typename ID>
bool Task<ID>::isOptional() const {
    return optional;
}

template<typename ID>
void Task<ID>::setOptional(const bool &optional) {
    Task::optional = optional;
}

template<typename ID>
const std::set<ID> &Task<ID>::getGroups() const {
    return groups;
}

template<typename ID>
void Task<ID>::addTag(const ID &ID) {

    tags[ID] = 0;
}

template<typename ID>
void Task<ID>::removeTag(const ID &ID) {

    tags.erase(ID);
}

template<typename ID>
bool Task<ID>::inGroup(const ID &group) const {
    return groups.count(group);
}
*/

#endif //OMTSCHED_TASK_H
