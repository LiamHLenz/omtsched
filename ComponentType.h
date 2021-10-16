//
// Created by hal on 02.10.21.
//

#ifndef OMTSCHED_COMPONENTTYPE_H
#define OMTSCHED_COMPONENTTYPE_H

namespace omtsched {

    template<typename ID>
    class ComponentType{

    public:
        ComponentType(const ID &id);
        const ID &getID() const;
        const ID id;
    };

    template<typename ID>
    const ID &ComponentType<ID>::getID() const {
        return id;
    }

    template<typename ID>
    ComponentType<ID>::ComponentType(const ID &id) : id{id} {}

    template<typename ID>
    class Agent : public ComponentType<ID> {
    public:
        Agent(const ID &id) : ComponentType<ID>(id) {};
    };

    template<typename ID>
    class Task : public ComponentType<ID> {
    public:
        Task(const ID &id) : ComponentType<ID>(id) {};
    };

    template<typename ID>
    class Timeslot : public ComponentType<ID> {
    public:
        Timeslot(const ID &id) : ComponentType<ID>(id) {};
    };

    template<typename ID, typename Unit>
    class Time : public ComponentType<ID> {
    public:
        Time(const ID &id) : ComponentType<ID>(id) {};
    };

    template<typename ID, typename Unit>
    class TimedTask : public Timeslot<ID> {};

}

#endif //OMTSCHED_COMPONENTTYPE_H
