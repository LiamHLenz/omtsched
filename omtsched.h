#ifndef OMTSCHED_OMTSCHED_H
#define OMTSCHED_OMTSCHED_H

#include "Problem.h"

void hello();

namespace omtsched {


    template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
    void saveEncoding(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem);

    template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
    bool solve(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem);

    // getSchedule();
    // getExplanation();

}



#endif //OMTSCHED_OMTSCHED_H
