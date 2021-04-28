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

    Task(const ID &id, const Timepoint &start, const Duration &duration,
            const Timepoint &deadline = boost::date_time::neg_infin, bool optional = false);

    void addGroup(const GroupID &group);

    void removeGroup(const GroupID &group);

    [[nodiscard]] const std::set<GroupID> &getGroups() const;

    void setTagPriority(const TagID &tag, const int &priority);

    [[nodiscard]] const int &getTagPriority(const TagID &tag) const;

    [[nodiscard]] const ID getTaskId() const;

    [[nodiscard]] const Timepoint &getStartPoint() const;

    void setStartPoint(const Timepoint &startPoint);

    [[nodiscard]] const Timepoint &getDeadline() const;

    void setDeadline(const Timepoint &deadline);

    [[nodiscard]] const Duration &getDuration() const;

    void setDuration(const Duration &duration);

    [[nodiscard]] bool isOptional() const;

    void setOptional(bool optional);

private:

    const ID taskID;
    Timepoint startPoint;
    Timepoint deadline;
    Duration duration;
    std::set<GroupID> groups;
    std::map<TagID, int> tags;
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
void Task<ID, GroupID, TagID>::addGroup(const GroupID &group) {

    groups.insert(group);

}

template<typename ID, typename GroupID, typename TagID>
void Task<ID, GroupID, TagID>::removeGroup(const GroupID &group) {

    groups.erase(group);
}

template<typename ID, typename GroupID, typename TagID>
void Task<ID, GroupID, TagID>::setTagPriority(const TagID &tag, const int &priority) {

    tags.at(tag) = priority;
}

template<typename ID, typename GroupID, typename TagID>
const int &Task<ID, GroupID, TagID>::getTagPriority(const TagID &tag) const {
    return tag.at(tag);
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
void Task<ID, GroupID, TagID>::setOptional(bool optional) {
    Task::optional = optional;
}

template<typename ID, typename GroupID, typename TagID>
const std::set<GroupID> &Task<ID, GroupID, TagID>::getGroups() const {
    return groups;
}


#endif //OMTSCHED_TASK_H
