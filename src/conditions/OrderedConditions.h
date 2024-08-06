//
// Created by hal on 07.11.21.
//

#ifndef OMTSCHED_ORDEREDCONDITIONS_H
#define OMTSCHED_ORDEREDCONDITIONS_H

#include <vector>
#include "../omtsched.h"

namespace omtsched {


    template<typename ID>
    class Blocked : public NamedCondition<ID> {

    public:
        void print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const override;
        void declareVariables(std::ostream &, const std::vector<Assignment<ID>*> &) const override;
        virtual const CONDITION_TYPE getType() const override;

        Blocked(ID componentSlot, std::vector<std::shared_ptr<Condition<ID>>> subconditions = {}) :
            NamedCondition<ID>(componentSlot, subconditions) {};
    };

    template<typename ID>
    std::shared_ptr<Condition<ID>> blocked(ID componentSlot, std::vector<std::shared_ptr<Condition<ID>>> subconditions) {
        return std::make_shared<Blocked<ID>>(componentSlot, subconditions);
    }

template<typename ID>
const omtsched::CONDITION_TYPE omtsched::Blocked<ID>::getType() const {
    return omtsched::CONDITION_TYPE::BLOCKED;
}


template<typename ID>
    void Blocked<ID>::declareVariables(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgn) const {

        ostr << "(declare-fun block" << this->getNamedSlot() << " () (_ BitVec " << asgn.size() << "))" << std::endl;

    }


    template<typename ID>
    void Blocked<ID>::print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const {


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


    template<typename ID>
    class Greater : public NamedCondition<ID> {

    public:
        void print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const override;
        void declareVariables(std::ostream &, const std::vector<Assignment<ID>*> &) const override;
        virtual const CONDITION_TYPE getType() const override;

        Greater(ID componentSlot, std::vector<std::shared_ptr<Condition<ID>>> subconditions = {}) :
            NamedCondition<ID>(componentSlot, subconditions) {};

        const ID componentSlot;
        int n;
    };

    template<typename ID>
    std::shared_ptr<Condition<ID>> greater(ID componentSlot, std::shared_ptr<Condition<ID>> s1, std::shared_ptr<Condition<ID>> s2) {
        return std::make_shared<Greater<ID>>(componentSlot, std::vector<std::shared_ptr<Condition<ID>>> {s1, s2});
    }

    template<typename ID>
    const omtsched::CONDITION_TYPE omtsched::Greater<ID>::getType() const {
        return omtsched::CONDITION_TYPE::GREATER;
    }


    template<typename ID>
    void Greater<ID>::declareVariables(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgn) const {
        //TODO
    }


    template<typename ID>
    void Greater<ID>::print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const {
        //TODO
    }

}


#endif //OMTSCHED_ORDEREDCONDITIONS_H
