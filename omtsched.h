#ifndef OMTSCHED_OMTSCHED_H
#define OMTSCHED_OMTSCHED_H

#include "Problem.h"
#include "z3/TranslatorZ3.h"
#include <fstream>


namespace omtsched {

    template<typename TaskID, typename TimeslotID, typename ID, typename ID>
    void saveEncoding(const Problem<TaskID, ID, ID> &problem);

    // getSchedule();
    // getExplanation();

}

#include "omtsched.hpp"

#endif //OMTSCHED_OMTSCHED_H
