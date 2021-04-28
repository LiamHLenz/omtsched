//
// Created by dana on 26.04.21.
//

#ifndef OMTSCHED_TIMESLOT_H
#define OMTSCHED_TIMESLOT_H

#include <string>
#include <map>
#include <set>
#include <boost/date_time/posix_time/ptime.hpp>

template<typename ID, typename GroupID, typename TagID>
class Timeslot {

    // Abbreviating long typenames, mainly to keep constructor arguments readable
    using Timepoint = boost::posix_time::ptime;
    using Duration = boost::posix_time::time_duration;

public:

    Timeslot(const ID &tsID, const Timepoint &startTime, const Duration &duration);

    const ID &getID() const;



private:

    const ID timeslotID;
    boost::posix_time::ptime start;
    boost::posix_time::time_duration duration;
    std::map<GroupID, int> tags;
    std::set<TagID> groups;
};


#endif //OMTSCHED_TIMESLOT_H
