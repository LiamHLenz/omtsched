#ifndef OMTSCHED_OMTSCHED_H
#define OMTSCHED_OMTSCHED_H

#include "Problem.h"
#include "Translator.h"
#include <fstream>

void hello();

namespace omtsched {

    template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
    void saveEncoding(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem);

    // getSchedule();
    // getExplanation();

}

#include "omtsched.hpp"

#endif //OMTSCHED_OMTSCHED_H
