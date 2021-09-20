//
// Created by dana on 26.04.21.
//

#ifndef OMTSCHED_TIMESLOT_H
#define OMTSCHED_TIMESLOT_H

#include "Time.h"

namespace omtsched {
    template<class ComponentID, class TagID, class GroupID, class Unit>
    class Timeslot : public Time<ComponentID, TagID, GroupID, Unit> {
    };

}
/*
template<typename ID, typename GroupID, typename TagID>
class Timeslot {

    // Abbreviating long typenames, mainly to keep constructor arguments readable
    using Timepoint = boost::posix_time::ptime;
    using Duration = boost::posix_time::time_duration;

public:

    Timeslot(const ID &tsID, const Timepoint &startTime, const Duration &duration);

    [[nodiscard]] const ID getID() const;

    [[nodiscard]] const Timepoint getStartPoint() const;

    void setStartPoint(const Timepoint &startPoint);

    [[nodiscard]] const Duration getDuration() const;

    void setDuration(const Duration &duration);

    void addGroup(const GroupID &group);

    bool removeGroup(const GroupID &group);

    bool inGroup(const GroupID &group) const;

    [[nodiscard]] const std::set<GroupID> &getGroups() const;

    void setTagPriority(const TagID &tag, const unsigned int &priority);

    [[nodiscard]] const int getTagPriority(const TagID &tag) const;

    void addTag(const TagID &tagID);

    void removeTag(const TagID &tagID);



private:

    const ID timeslotID;
    boost::posix_time::ptime start;
    boost::posix_time::time_duration duration;
    std::map<TagID, unsigned int> tags;
    std::set<GroupID> groups;
};

template<typename ID, typename GroupID, typename TagID>
Timeslot<ID, GroupID, TagID>::Timeslot(const ID &tsID, const Timeslot::Timepoint &startTime,
                                       const Timeslot::Duration &duration)
                                       : timeslotID{tsID}, start{startTime}, duration{duration} {}

template<typename ID, typename GroupID, typename TagID>
const ID Timeslot<ID, GroupID, TagID>::getID() const {
    return timeslotID;
}

template<typename ID, typename GroupID, typename TagID>
const boost::posix_time::ptime Timeslot<ID, GroupID, TagID>::getStartPoint() const {
    return start;
}

template<typename ID, typename GroupID, typename TagID>
void Timeslot<ID, GroupID, TagID>::setStartPoint(const Timeslot::Timepoint &startPoint) {
    start = startPoint;
}

template<typename ID, typename GroupID, typename TagID>
const boost::posix_time::time_duration Timeslot<ID, GroupID, TagID>::getDuration() const {
    return duration;
}

template<typename ID, typename GroupID, typename TagID>
void Timeslot<ID, GroupID, TagID>::setDuration(const Timeslot::Duration &duration) {

    this->duration = duration;
}

template<typename ID, typename GroupID, typename TagID>
void Timeslot<ID, GroupID, TagID>::addGroup(const GroupID &group) {

    groups.insert(group);
}

template<typename ID, typename GroupID, typename TagID>
bool Timeslot<ID, GroupID, TagID>::removeGroup(const GroupID &group) {

    if(!groups.count(group))
        return false;
    else
        groups.erase(group);

    return true;
}

template<typename ID, typename GroupID, typename TagID>
const std::set<GroupID> &Timeslot<ID, GroupID, TagID>::getGroups() const {
    return groups;
}

template<typename ID, typename GroupID, typename TagID>
bool Timeslot<ID, GroupID, TagID>::inGroup(const GroupID &group) const {
    return groups.count(group);
}

template<typename ID, typename GroupID, typename TagID>
void Timeslot<ID, GroupID, TagID>::setTagPriority(const TagID &tag, const unsigned int &priority) {

    tags.at(tag) = priority;
}

template<typename ID, typename GroupID, typename TagID>
const int Timeslot<ID, GroupID, TagID>::getTagPriority(const TagID &tag) const {
    int test = tags.at(tag);
    return test;
    //return tags.at(tag);
}

template<typename ID, typename GroupID, typename TagID>
void Timeslot<ID, GroupID, TagID>::addTag(const TagID &tagID) {

    // Todo: Tag already exists
    //if(tags.count(tagID))

    tags.insert(std::pair(tagID, 0));
}

template<typename ID, typename GroupID, typename TagID>
void Timeslot<ID, GroupID, TagID>::removeTag(const TagID &tagID) {

    tags.erase(tagID);
} */

#endif //OMTSCHED_TIMESLOT_H
