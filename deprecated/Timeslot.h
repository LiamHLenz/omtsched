//
// Created by dana on 26.04.21.
//

#ifndef OMTSCHED_TIMESLOT_H
#define OMTSCHED_TIMESLOT_H

#include "Time.h"
/*
namespace omtsched {
    template<typename ID>
    class Timeslot : public Component<ID> {
    };

}

template<typename ID>
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

    void addGroup(const ID &group);

    bool removeGroup(const ID &group);

    bool inGroup(const ID &group) const;

    [[nodiscard]] const std::set<ID> &getGroups() const;

    void setTagPriority(const ID &tag, const unsigned int &priority);

    [[nodiscard]] const int getTagPriority(const ID &tag) const;

    void addTag(const ID &ID);

    void removeTag(const ID &ID);



private:

    const ID timeslotID;
    boost::posix_time::ptime start;
    boost::posix_time::time_duration duration;
    std::map<ID, unsigned int> tags;
    std::set<ID> groups;
};

template<typename ID>
Timeslot<ID>::Timeslot(const ID &tsID, const Timeslot::Timepoint &startTime,
                                       const Timeslot::Duration &duration)
                                       : timeslotID{tsID}, start{startTime}, duration{duration} {}

template<typename ID>
const ID Timeslot<ID>::getID() const {
    return timeslotID;
}

template<typename ID>
const boost::posix_time::ptime Timeslot<ID>::getStartPoint() const {
    return start;
}

template<typename ID>
void Timeslot<ID>::setStartPoint(const Timeslot::Timepoint &startPoint) {
    start = startPoint;
}

template<typename ID>
const boost::posix_time::time_duration Timeslot<ID>::getDuration() const {
    return duration;
}

template<typename ID>
void Timeslot<ID>::setDuration(const Timeslot::Duration &duration) {

    this->duration = duration;
}

template<typename ID>
void Timeslot<ID>::addGroup(const ID &group) {

    groups.insert(group);
}

template<typename ID>
bool Timeslot<ID>::removeGroup(const ID &group) {

    if(!groups.count(group))
        return false;
    else
        groups.erase(group);

    return true;
}

template<typename ID>
const std::set<ID> &Timeslot<ID>::getGroups() const {
    return groups;
}

template<typename ID>
bool Timeslot<ID>::inGroup(const ID &group) const {
    return groups.count(group);
}

template<typename ID>
void Timeslot<ID>::setTagPriority(const ID &tag, const unsigned int &priority) {

    tags.at(tag) = priority;
}

template<typename ID>
const int Timeslot<ID>::getTagPriority(const ID &tag) const {
    int test = tags.at(tag);
    return test;
    //return tags.at(tag);
}

template<typename ID>
void Timeslot<ID>::addTag(const ID &ID) {

    // Todo: Tag already exists
    //if(tags.count(ID))

    tags.insert(std::pair(ID, 0));
}

template<typename ID>
void Timeslot<ID>::removeTag(const ID &ID) {

    tags.erase(ID);
} */

#endif //OMTSCHED_TIMESLOT_H
