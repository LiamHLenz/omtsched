//
// Created by dana on 21.05.21.
//

#ifndef OMTSCHED_MODEL_H
#define OMTSCHED_MODEL_H

#include "Problem.h"

template<typename ID>
class Model {

    // A model must assign a component to each component slot a component
    // TODO: empty assignments -> NONE component?
public:
    void set(const ID &assignment, const std::string &slot, const ID &component);
    const ID &get(const ID &assignment, const std::string &slot);

    void addPenalty(const int &);
    int getPenalty() const;

private:
    // map between (assignment, slotName) and components
    std::map<std::pair<ID, std::string>, ID> assignments;

    int penalty;
};

template<typename ID>
void Model<ID>::set(const ID &assignment, const std::string &slot, const ID &component) {
    assignments[assignment, slot] = component;
}

template<typename ID>
const ID &Model<ID>::get(const ID &assignment, const std::string &slot) {
    return assignments.at({assignment, slot});
}

template<typename ID>
void Model<ID>::addPenalty(const int &p) {
    penalty += p;
}

template<typename ID>
int Model<ID>::getPenalty() const {
    return penalty;
}

#endif //OMTSCHED_MODEL_H
