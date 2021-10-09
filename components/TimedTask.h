//
// Created by hal on 04.09.21.
//

#ifndef OMTSCHED_TIMEDTASK_H
#define OMTSCHED_TIMEDTASK_H

#include "Timeslot.h"

namespace omtsched {
    template<class ID, class ID, class ID, class Unit>
    class TimedTask : public Timeslot<ID, ID, ID, Unit> {
    };

}
#endif //OMTSCHED_TIMEDTASK_H
