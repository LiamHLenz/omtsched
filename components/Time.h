//
// Created by hal on 04.09.21.
//

#ifndef OMTSCHED_TIME_H
#define OMTSCHED_TIME_H

#include "../Component.h"

namespace omtsched {
    template<class ID, class ID, class ID, class Unit>
    class Time : public Component<ID> {

    public:
        Unit getTimepoint() const;

        void setTimepoint(Unit timepoint);

    private:
        Unit timepoint;

    };

    template<class ID, class ID, class ID, class Unit>
    Unit Time<ID, ID, ID, Unit>::getTimepoint() const {
        return timepoint;
    }

    template<class ID, class ID, class ID, class Unit>
    void Time<ID, ID, ID, Unit>::setTimepoint(Unit timepoint) {
        Time::timepoint = timepoint;
    }
}

template<class ID, class ID, class ID, class Unit>
bool operator<(const omtsched::Time<ID, ID, ID, Unit> &lhs, const omtsched::Time<ID, ID, ID, Unit> &rhs) {

    return lhs.getTimepoint() < rhs.getTimepoint();
}

#endif //OMTSCHED_TIME_H
