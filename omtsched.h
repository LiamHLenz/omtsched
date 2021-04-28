#ifndef OMTSCHED_OMTSCHED_H
#define OMTSCHED_OMTSCHED_H

#include <string>
#include "Task.h"
#include "Timeslot.h"

void hello();

namespace omtsched {

    using Timepoint = boost::posix_time::ptime;
    using Duration = boost::posix_time::time_duration;

    template<typename ID, typename GroupID, typename TagID>
    Task<ID, GroupID, TagID>* addTask(const ID &id);

    template<typename ID>
    bool deleteTask(const ID &id);

    template<typename groupID>
    void addGroup(const groupID &);

    template<typename groupID>
    void deleteGroup(const groupID &);

    template<typename tagID>
    void addTag(const tagID &id);

    template<typename tagID>
    void deleteTag(const tagID &id);

    void saveEncoding();

    bool solve();

    // getSchedule();
    // getExplanation();

}



#endif //OMTSCHED_OMTSCHED_H
