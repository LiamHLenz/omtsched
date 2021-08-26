//
// Created by dana on 26.04.21.
//

#ifndef OMTSCHED_TASK_H
#define OMTSCHED_TASK_H

#include <boost/date_time.hpp>
#include <set>
#include <map>


template<typename ID, typename GroupID, typename TagID>
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
    Task(const ID &id, const Timepoint &start, const Duration &duration,
            const Timepoint &deadline = boost::date_time::neg_infin, bool optional = false);

    /**
     * Tasks can belong to groups, being of the same type or belonging to a collection
     * of some form. They exist to create constraints and optimality criteria
     * and help find patterns of failure.
     * @param group ID of the group to add. The group needs to be registered using addGroup() before.
     */
    bool addGroup(const GroupID &group);

    bool removeGroup(const GroupID &group);

    bool inGroup(const GroupID &group) const;

    [[nodiscard]] const std::set<GroupID> &getGroups() const;

    bool setTagPriority(const TagID &tag, const unsigned int &priority);

    [[nodiscard]] const int getTagPriority(const TagID &tag) const;

    [[nodiscard]] const ID getTaskId() const;

    [[nodiscard]] const Timepoint &getStartPoint() const;

    void setStartPoint(const Timepoint &startPoint);

    [[nodiscard]] const Timepoint &getDeadline() const;

    void setDeadline(const Timepoint &deadline);

    [[nodiscard]] const Duration &getDuration() const;

    void setDuration(const Duration &duration);

    [[nodiscard]] bool isOptional() const;

    void setOptional(const bool &optional);

    void addTag(const TagID &tagID);

    void removeTag(const TagID &tagID);

private:

    const ID taskID;
    Timepoint startPoint;
    Timepoint deadline;
    Duration duration;
    std::set<GroupID> groups;
    std::map<TagID, unsigned int> tags;
    bool optional;

};


template <typename ID, typename GroupID, typename TagID>
Task<ID, GroupID, TagID>::Task(const ID &id, const Task::Timepoint &start, const Task::Duration &duration,
                               const Task::Timepoint &deadline, bool optional)
        : taskID{id}, startPoint{start}, duration{duration}, deadline{deadline}, optional{optional} {

    // for(auto &tagID : getAllTags())
    //    tags[tagID] = 1;
}


template<typename ID, typename GroupID, typename TagID>
bool Task<ID, GroupID, TagID>::addGroup(const GroupID &group) {

    //if(!allGroups().count())
    //  return false;

    groups.insert(group);
    return true;

}

template<typename ID, typename GroupID, typename TagID>
bool Task<ID, GroupID, TagID>::removeGroup(const GroupID &group) {

    groups.erase(group);
}

template<typename ID, typename GroupID, typename TagID>
bool Task<ID, GroupID, TagID>::setTagPriority(const TagID &tag, const unsigned  int &priority) {

    if(!tags.count(tag))
        return false;

    tags.at(tag) = priority;

    return true;
}

template<typename ID, typename GroupID, typename TagID>
const int Task<ID, GroupID, TagID>::getTagPriority(const TagID &tag) const {

    if(!tags.count(tag))
        return -1;

    return tags.at(tag);
}

template<typename ID, typename GroupID, typename TagID>
const ID Task<ID, GroupID, TagID>::getTaskId() const {
    return taskID;
}

template<typename ID, typename GroupID, typename TagID>
const boost::posix_time::ptime &Task<ID, GroupID, TagID>::getStartPoint() const {
    return startPoint;
}

template<typename ID, typename GroupID, typename TagID>
void Task<ID, GroupID, TagID>::setStartPoint(const Task::Timepoint &startPoint) {
    Task::startPoint = startPoint;
}

template<typename ID, typename GroupID, typename TagID>
const boost::posix_time::ptime &Task<ID, GroupID, TagID>::getDeadline() const {
    return deadline;
}

template<typename ID, typename GroupID, typename TagID>
void Task<ID, GroupID, TagID>::setDeadline(const Task::Timepoint &deadline) {
    Task::deadline = deadline;
}

template<typename ID, typename GroupID, typename TagID>
const boost::posix_time::time_duration &Task<ID, GroupID, TagID>::getDuration() const {
    return duration;
}

template<typename ID, typename GroupID, typename TagID>
void Task<ID, GroupID, TagID>::setDuration(const Task::Duration &duration) {
    Task::duration = duration;
}

template<typename ID, typename GroupID, typename TagID>
bool Task<ID, GroupID, TagID>::isOptional() const {
    return optional;
}

template<typename ID, typename GroupID, typename TagID>
void Task<ID, GroupID, TagID>::setOptional(const bool &optional) {
    Task::optional = optional;
}

template<typename ID, typename GroupID, typename TagID>
const std::set<GroupID> &Task<ID, GroupID, TagID>::getGroups() const {
    return groups;
}

template<typename ID, typename GroupID, typename TagID>
void Task<ID, GroupID, TagID>::addTag(const TagID &tagID) {

    tags[tagID] = 0;
}

template<typename ID, typename GroupID, typename TagID>
void Task<ID, GroupID, TagID>::removeTag(const TagID &tagID) {

    tags.erase(tagID);
}

template<typename ID, typename GroupID, typename TagID>
bool Task<ID, GroupID, TagID>::inGroup(const GroupID &group) const {
    return groups.count(group);
}


#endif //OMTSCHED_TASK_H
