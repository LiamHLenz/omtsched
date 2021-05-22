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

    bool solveZ3(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem);
    //void interpretModelZ3(z3::model, Model &model);
    void outputModelZ3(z3::model);

    const char* makeID(const std::string &type, const size_t &number, const std::string &attribute) const;
    const char* makeID(const std::string &type, const size_t &num1, const std::string &attribute, const size_t &num2) const;


    const std::string assigned(const size_t &tid, const size_t &aid) const;
    int timeInUnit(const Unit &unit, const boost::posix_time::time_duration &duration) const;
    int timeBetween(const Unit &unit, const boost::posix_time::ptime &first, const boost::posix_time::ptime &second) const;

    // ----------------------------------
    std::map<TaskID, size_t> task_id;
    std::map<TimeslotID, size_t> ts_id;
    std::map<TagID, size_t> tag_id;
    std::map<GroupID, size_t> group_id;

    //-- datastructures for Z3 ----------
    std::map<TaskID, std::vector<z3::expr>> task_expr;
    std::map<TimeslotID, std::vector<z3::expr>> ts_expr;
    std::map<std::pair<TimeslotID, TagID>, z3::expr> assign_expr;

    std::map<TaskID, std::vector<z3::expr>> task_tags;
    std::map<TaskID, std::vector<z3::expr>> task_groups;
    std::map<TimeslotID, std::vector<z3::expr>> ts_tags;
    std::map<TimeslotID, std::vector<z3::expr>> ts_groups;

    enum TaskAttributes {
        Start = 0,
        Duration = 1,
        Deadline = 2,
        Optional = 3
    };

    enum TSAttributes {
        Start = 0,
        Duration = 1
    };

};

#include "Translator.hpp"

#endif //OMTSCHED_TRANSLATOR_H
