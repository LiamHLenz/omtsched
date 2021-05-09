#ifndef OMTSCHED_OMTSCHED_H
#define OMTSCHED_OMTSCHED_H

#include "Problem.h"
#include <fstream>

void hello();

namespace omtsched {

    enum class Solver {
        Z3
    };


    template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
    void saveEncoding(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem);

    template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
    bool solve(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem, const Solver &solver);

    // getSchedule();
    // getExplanation();

}

#include "omtsched.hpp"

#endif //OMTSCHED_OMTSCHED_H
