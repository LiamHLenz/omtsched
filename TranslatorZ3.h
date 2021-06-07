//
// Created by dana on 11.05.21.
//

#ifndef OMTSCHED_TRANSLATORZ3_H
#define OMTSCHED_TRANSLATORZ3_H


#include "Translator.h"
#include <z3.h>
#include <z3++.h>

template <typename Key1, typename Key2>
class expr_map {

public:
    const z3::expr get(const Key1 &key1, const Key2 &key2) const;
    void set(const Key1 &key1, const Key2 &key2, z3::expr expr);

private:
    std::map<std::pair<Key1, Key2>, std::vector<z3::expr>> internal_map;

};


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
class TranslatorZ3 : public Translator<TaskID, TimeslotID, GroupID, TagID> {

public:

    bool solve(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem) override;


private:

    //void interpretModelZ3(z3::model, Model &model);
    void outputModelZ3(z3::model);


    /*
    const std::string assigned(const size_t &tid, const size_t &aid) const;

    const char* makeID(const std::string &type, const size_t &number, const std::string &attribute) const;
    const char* makeID(const std::string &type, const size_t &num1, const std::string &attribute, const size_t &num2) const;

    int timeInUnit(const Unit &unit, const boost::posix_time::time_duration &duration) const;
    int timeBetween(const Unit &unit, const boost::posix_time::ptime &first, const boost::posix_time::ptime &second) const;

    // ----------------------------------
    std::map<TaskID, size_t> task_id;
    std::map<TimeslotID, size_t> ts_id;
    std::map<TagID, size_t> tag_id;
    std::map<GroupID, size_t> group_id; */

    //-- datastructures for Z3 ----------

    // This should work better
    std::map<TaskID, std::vector<z3::expr>> task_expr;
    std::map<TimeslotID, std::vector<z3::expr>> ts_expr;

    // These are tricky, since z3 has no default constructor, which is needed by map
    // Implementation subject to change, hence encapsulation in own class
    expr_map<TimeslotID, TagID> assign_expr;

    expr_map<TaskID, TagID> task_tags;
    expr_map<TaskID, GroupID> task_groups;
    expr_map<TimeslotID, TagID> ts_tags;
    expr_map<TimeslotID, GroupID> ts_groups;


    enum Attributes {
        Start = 0,
        Duration = 1,
        Deadline = 2,
        Optional = 3
    };

};

#include "TranslatorZ3.hpp"

#endif //OMTSCHED_TRANSLATORZ3_H
