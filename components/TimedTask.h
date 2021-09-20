//
// Created by hal on 04.09.21.
//

#ifndef OMTSCHED_TIMEDTASK_H
#define OMTSCHED_TIMEDTASK_H

#include "Timeslot.h"

namespace omtsched {
    template<class ComponentID, class TagID, class GroupID, class Unit>
    class TimedTask : public Timeslot<ComponentID, TagID, GroupID, Unit> {
    };

}
#endif //OMTSCHED_TIMEDTASK_H
