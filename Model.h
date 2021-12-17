//
// Created by dana on 21.05.21.
//

#ifndef OMTSCHED_MODEL_H
#define OMTSCHED_MODEL_H

#include "Problem.h"

namespace omtsched {

    template<typename ID>
    class Model {

        // A model must assign a component to each component slot a component
        // TODO: empty assignments -> NONE component?
    public:
        void setComponent(const ID &assignment, const std::string &slot, const ID &component);

        const ID &getComponent(const ID &assignment, const std::string &slot);

        void addPenalty(const int &);

        int getPenalty() const;

        void print(std::ostream &ostr) const;

    private:
        // map between (assignment, slotName) and components
        std::map<std::pair<ID, ID>, ID> assignments;
        int penalty;
    };

    template<typename ID>
    void Model<ID>::setComponent(const ID &assignment, const std::string &slot, const ID &component) {
        assignments[std::make_pair(assignment, slot)] = component;
    }

    template<typename ID>
    const ID &Model<ID>::getComponent(const ID &assignment, const std::string &slot) {
        return assignments.at(std::make_pair(assignment, slot));
    }

    template<typename ID>
    void Model<ID>::addPenalty(const int &p) {
        penalty += p;
    }

    template<typename ID>
    int Model<ID>::getPenalty() const {
        return penalty;
    }

    template<typename ID>
    void Model<ID>::print(std::ostream &ostr) const {

        ostr << "MODEL START" << std::endl;
        // std::map<std::pair<ID, ID>, ID> assignments;
        for(const auto &[pair, assigned] : assignments)
            ostr << "(" << pair.first << ", " << pair.second << ") -> " << assigned << std::endl;

        ostr << "MODEL END" << std::endl;
    }

}

#endif //OMTSCHED_MODEL_H
