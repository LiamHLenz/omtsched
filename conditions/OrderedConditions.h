//
// Created by hal on 07.11.21.
//

#ifndef OMTSCHED_ORDEREDCONDITIONS_H
#define OMTSCHED_ORDEREDCONDITIONS_H

#include "../Condition.h"

namespace omtsched {


    template<typename ID>
    class Blocked : public NamedCondition<ID> {

    public:
        void print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const override;
        void declareVariables(std::ostream &ostr, std::vector<Assignment<ID>*> &asgns, const int n) const override;

        Blocked(ID componentSlot, std::shared_ptr<Condition<ID>> subconditions) : componentSlot{componentSlot},
                                                      subconditions{subconditions}, n{0} {};

        const ID componentSlot;
        const std::shared_ptr<Condition<ID>> subcondition;
        int n;
    };

    template<typename ID>
    std::shared_ptr<Condition<ID>> blocked(ID componentSlot, std::shared_ptr<Condition<ID>> subcondition) {
        return std::make_shared<Blocked<ID>>(componentSlot, subcondition);
    }

    void Blocked<ID>::declareVariables(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const {

        ostr << "(declare-fun block" << id << "n" << n << " () (_ BitVec " << asgns.size() << "))" << std::endl;
        n++;
    }

    template<typename ID>
    void Blocked<ID>::print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) {


        // recognize 0*1*0*
        // shift left and xor, disregard rightmost: hamming weight of 0-2 legal (measure changes)
        // same with right shift

        // 00011100
        // 00111000
        // 00100100

        // (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
        // (declare-fun a () (_ BitVec 32))

        // TODO: for every bitvector constraint, declare variable at top of
        // each bitvector constraint needs an id
        //ostr << "(declare-fun bl" <<  << "(_ BitVec " << asgns.size() << "))"

    }


}


#endif //OMTSCHED_ORDEREDCONDITIONS_H
