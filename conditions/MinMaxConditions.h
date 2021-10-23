//
// Created by Betrieb-PC on 20.10.2021.
//

#ifndef OMTSCHED_MINMAXCONDITIONS_H
#define OMTSCHED_MINMAXCONDITIONS_H

#include "../Condition.h"

namespace omtsched {

    template<typename ID>
    class MaxAssignment : public Condition<ID> {

    public:
        MaxAssignment(const int &max, std::vector<Condition<ID>> sc) : max{ max }, subconditions{std::move(sc)} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::MAX_ASSIGNMENTS;
        const int max;
        const std::vector<Condition<ID>> subconditions;

    };

    template<typename ID>
    class MaxInSequence : public Condition<ID> {

    public:
        MaxInSequence(const int &max, const int &sequenceLength, std::vector<Condition<ID>> sc) : max{ max }, sequenceLength{sequenceLength}, subconditions{std::move(sc)} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::MAX_IN_SEQUENCE;
        const int max;
        const int sequenceLength;
        const std::vector<Condition<ID>> subconditions;

    };


}


#endif //OMTSCHED_MINMAXCONDITIONS_H
