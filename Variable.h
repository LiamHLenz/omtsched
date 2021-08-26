//
// Created by admin on 26.08.2021.
//

#ifndef OMTSCHED_VARIABLE_H
#define OMTSCHED_VARIABLE_H


template<class Domain>
class Variable {

    bool finite;
    std::set<Domain> domain;

};

#endif //OMTSCHED_VARIABLE_H
