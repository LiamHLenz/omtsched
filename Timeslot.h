//
// Created by dana on 26.04.21.
//

#ifndef OMTSCHED_TIMESLOT_H
#define OMTSCHED_TIMESLOT_H

#include <string>
#include <map>
#include <set>
#include <boost/date_time/posix_time/ptime.hpp>

template<typename ID>
class Timeslot {

    ID timeslotID;
    boost::posix_time::ptime start;
    boost::posix_time::time_duration duration;
    std::map<ID, int> tags;
    std::set<ID> groups;
};


#endif //OMTSCHED_TIMESLOT_H
