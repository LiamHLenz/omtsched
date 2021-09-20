//
// Created by hal on 04.09.21.
//

#ifndef OMTSCHED_TIME_H
#define OMTSCHED_TIME_H

#include "../Component.h"

namespace omtsched {
    template<class ComponentID, class TagID, class GroupID, class Unit>
    class Time : public Component<ComponentID, TagID, GroupID> {

    public:
        Unit getTimepoint() const;

        void setTimepoint(Unit timepoint);

    private:
        Unit timepoint;

    };

    template<class ComponentID, class TagID, class GroupID, class Unit>
    Unit Time<ComponentID, TagID, GroupID, Unit>::getTimepoint() const {
        return timepoint;
    }

    template<class ComponentID, class TagID, class GroupID, class Unit>
    void Time<ComponentID, TagID, GroupID, Unit>::setTimepoint(Unit timepoint) {
        Time::timepoint = timepoint;
    }
}

template<class ComponentID, class TagID, class GroupID, class Unit>
bool operator<(const omtsched::Time<ComponentID, TagID, GroupID, Unit> &lhs, const omtsched::Time<ComponentID, TagID, GroupID, Unit> &rhs) {

    return lhs.getTimepoint() < rhs.getTimepoint();
}

#endif //OMTSCHED_TIME_H
