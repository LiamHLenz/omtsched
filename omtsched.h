#ifndef OMTSCHED_OMTSCHED_H
#define OMTSCHED_OMTSCHED_H

#include "Problem.h"
#include "z3/TranslatorZ3.h"
#include <fstream>


namespace omtsched {

    template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
    void saveEncoding(const Problem<TaskID, GroupID, TagID> &problem);

    // getSchedule();
    // getExplanation();

}

#include "omtsched.hpp"

#endif //OMTSCHED_OMTSCHED_H
