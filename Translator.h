//
// Created by dana on 11.05.21.
//

#ifndef OMTSCHED_TRANSLATOR_H
#define OMTSCHED_TRANSLATOR_H


#include "Problem.h"
#include <z3.h>
#include <z3++.h>


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
class Translator {


public:

    enum class Solver {
        Z3
    };


    void saveEncoding(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem);
    bool solve(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem, const Solver &solver);


private:

    bool solveZ3(const Problem<TaskID, TimeslotID, GroupID, TagID> problem);
    const char* makeID(const std::string &type, const size_t &number, const std::string &attribute) const;
    const char* makeID(const std::string &type, const size_t &num1, const std::string &attribute, const size_t &num2) const;


    const std::string assigned(const size_t &tid, const size_t &aid) const;
    int timeInUnit(const Unit &unit, const boost::posix_time::time_duration &duration) const;
    int timeBetween(const Unit &unit, const boost::posix_time::ptime &first, const boost::posix_time::ptime &second) const;


    std::map<TaskID, size_t> task_id;
    std::map<TimeslotID, size_t> ts_id;
    std::map<TagID, size_t> tag_id;
    std::map<GroupID, size_t> group_id;


};

#include "Translator.hpp"

#endif //OMTSCHED_TRANSLATOR_H
