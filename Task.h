//
// Created by dana on 26.04.21.
//

#ifndef OMTSCHED_TASK_H
#define OMTSCHED_TASK_H

#include <boost/date_time.hpp>
#include <set>
#include <map>

template<typename ID>
class Task {

    ID taskID;
    boost::posix_time::ptime startPoint;
    boost::posix_time::ptime deadline;
    boost::posix_time::time_duration duration;
    std::set<ID> groups;
    std::map<ID, int> tags;
    bool optional;

};


#endif //OMTSCHED_TASK_H
