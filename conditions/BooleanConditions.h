//
// Created by Betrieb-PC on 06.10.2021.
//

#ifndef OMTSCHED_BOOLEANCONDITIONS_H
#define OMTSCHED_BOOLEANCONDITIONS_H

#include "../Condition.h"

namespace omtsched {
    //  ------------
    //      Not

    template<typename ID>
    class Not : public Condition<ID> {

    public:
        Not(const std::vector<Condition<ID>*> subconditions);
        virtual bool validParameters(std::vector<Component<ID>*>& arguments) override;
    };



    //  ------------
    //      And

    template<typename ID>
    class And : public Condition<ID> {

        public:
            And(const std::vector<Condition<ID>*> subconditions);
            virtual bool evaluate(std::vector<Component<ID>*>& arguments) override;
            virtual bool validParameters(std::vector<Component<ID>*>& arguments) override;
        };


    //  ------------
    //      Or

    template<typename ID>
    class Or : public Condition<ID> {

    public:
        Or() = default;
        Or(std::initializer_list<Condition<ID>> subconditions) : Condition<ID>(subconditions) {};
        void add(Condition<ID> &&);
        //virtual bool evaluate(std::vector<Component<ID>*>& arguments) override;

    };

    //TODO: see how move actually works
    template<typename ID>
    void Or<ID>::add(Condition <ID> && con) {
        this->subconditions.push_back(std::move(con));
    }


    //  ------------
    //    Implies

    template<typename ID>
    class Implies : public Condition<ID> {

        public:
            Implies(const std::vector<Condition<ID>*> subconditions);
            virtual bool evaluate(std::vector<Component<ID>*>& arguments) override;
        };

    template<typename ID>
    class Xor : public Condition<ID> {};

    template<typename ID>
    class Iff : public Condition<ID> {};

}
#endif //OMTSCHED_BOOLEANCONDITIONS_H
