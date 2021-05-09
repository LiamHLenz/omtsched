#include <iostream>
#include <utility>
#include <z3.h>
#include <z3++.h>

void hello() {
    std::cout << "Hello, World!" << std::endl;
}



int timeInUnit(const Unit &unit, const boost::posix_time::time_duration &duration) {

    switch (unit) {

        case Unit::HOURS:
            return duration.hours();

        case Unit::MINUTES:
            return duration.hours() *60 + duration.minutes();

        case Unit::SECONDS:
            return duration.hours()*60*60 + duration.minutes()*60 + duration.seconds();


    }

}


int timeBetween(const Unit &unit, const boost::posix_time::ptime &first, const boost::posix_time::ptime &second) {

    boost::posix_time::time_duration between = second - first;

    return timeInUnit(unit, between);

}



template <typename TimeslotID, typename TaskID>
std::string assignID(const TimeslotID &tsid, const TaskID &aid){

    return "assign_" + tsid + "_" + aid;

}


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
bool solveZ3(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem) {

    using namespace z3;

    enum {
        ID = 0, Start = 1, Duration = 2, Deadline = 3, Optional = 4
    };

    std::map<TaskID, std::vector<expr>> task_constants;
    std::map<TimeslotID, std::vector<expr>> ts_constants;
    std::map<std::pair<TaskID, GroupID>, expr> task_groups;
    std::map<std::pair<TaskID, TagID>, expr> task_tags;
    std::map<std::pair<TimeslotID, GroupID>, expr> ts_groups;
    std::map<std::pair<TimeslotID, TagID>, expr> ts_tags;
    std::map<std::pair<TimeslotID, TaskID>, expr> assignment_vars;
    std::set<expr> constraints;

    context c;

    auto start_point = problem.getStartPoint();
    auto unit = problem.getUnit();


    // Declare all variables
    for(const auto & [id, ts] : problem.getAllTimeslots()) {

        // ---- start time ------
        expr start = c.int_const(("t_" + id + "_start").c_str());
        ts_constants[id][Start] = start;
        //expr constraintStart = start == timeBetween(unit, start_point, ts.getStartPoint());
        //constraints.insert(constraintStart);
        constraints.emplace(start == timeBetween(unit, start_point, ts.getStartPoint()));

        expr duration = c.int_const(("t_" + id + "_duration").c_str());
        ts_constants[id][Duration] = duration;
        constraints.emplace(duration == timeInUnit(unit, ts.getDuration()));

        // Tags
        for(const auto & tag : problem.getAllTags()) {

            expr ttag = c.int_const(("t_" + id + "_tag_" + tag).c_str());
            //auto test = std::pair(id, tag);
            //ts_tags[test] = ttag;
            ts_tags[std::make_pair(id, tag)] = ttag;
            constraints.emplace(ttag == ts.getTagPriority(tag));

        }

        // Groups
        for(const auto & group : problem.getAllGroups()) {

            expr tgroup = c.bool_const(("t_" + id + "_group_" + group).c_str());
            ts_groups[std::pair(id, group)] = tgroup;

            if(ts.inGroup(group))
                constraints.emplace(tgroup);
            else
                constraints.emplace(!tgroup);
        }

    }

    for(const auto & [id, task] : problem.getAllTasks()) {

        expr start = c.int_const(("a_" + id  + "_start").c_str());
        task_constants[id][Start] = start;

        expr duration = c.int_const(("a_" + id + "_duration").c_str());
        task_constants[id][Duration] = duration;

        expr deadline =  c.int_const(("a_" + id + "_deadline").c_str());
        task_constants[id][Deadline] = deadline;

        expr optional = c.bool_const(("a_" + id + "_optional").c_str());
        task_constants[id][Optional] = optional;

        // Tags
        for(const auto & tag : problem.getAllTags()) {

            expr fun = c.int_const(("a_" + id + "_tag_" + tag).c_str());
            task_tags[std::pair(id, tag)] = fun;
            constraints.emplace(fun == task.getTagPriority(tag));

        }

        // Groups
        for(const auto & group : problem.getAllGroups()) {

            expr taskgroup = c.bool_const(("a_" + id + "_group_" + group).c_str());
            task_groups[std::pair(id, group)] = taskgroup;

            if(task.inGroup(group))
                constraints.emplace(taskgroup);
            else
                constraints.emplace(!taskgroup);

        }


    }

    // Assignment constraints
    // Add an "assigned" variable for all
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            assignment_vars[std::pair(tsid, aid)] = c.bool_const(("assign_" + tsid + "_" + aid).c_str());

    // 0. a timeslot cannot be double-booked
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            for(const auto &[aid2, action2] : problem.getAllTasks())
                if(aid != aid2)
                    constraints.emplace( implies(assignment_vars.at(std::pair(tsid, aid)), !assignment_vars.at(std::pair(tsid, aid2))));


    // 1. task cannot be scheduled before its start point
    for(const auto &[pair, expr] : assignment_vars) {

        const auto &task = problem.getTask(pair.second);
        const auto &ts = problem.getTimeslot(pair.first);

        constraints.emplace(implies(expr, timeBetween(unit, start_point, task.getStartPoint()) + timeInUnit(unit, task.getDuration())
                                       <= timeBetween(unit, start_point, ts.getStartPoint()) + timeInUnit(unit, ts.getDuration())));

    }


    // 2. Task execution cannot exceed its deadline


    // 3. Task duration cannot exceed timeslot duration


    // 4.

    auto s = solver(c);
    std::cout << s.check();

}


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
bool omtsched::solve(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem, const omtsched::Solver &solver) {

    switch (solver) {

        case omtsched::Solver::Z3 :
            return solveZ3(problem);

    }

}


template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void omtsched::saveEncoding(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem) {

    std::ofstream ostream(problem.problemName + ".smt2");

    ostream << "(set-logic QF_UFLIA)" << std::endl;
    ostream << "(set-option :produce-models true)" << std::endl;

    auto start = problem.getStartPoint();
    auto unit = problem.getUnit();

    for(const auto & [id, ts] : problem.getAllTimeslots()) {

        // ---- start time ------
        ostream << "(declare-fun t_" << id  << "_start () Int)      ; new timeslot" << std::endl;
        ostream << "(assert (= t_" << id << "_start " << timeBetween(unit, start, ts.getStartPoint()) << "))" << std::endl;

        ostream << "(declare-fun t_" << id << "_duration () Int)" << std::endl;
        ostream << "(assert (= t_" << id << "_duration " << timeInUnit(unit, ts.getDuration()) << "))" << std::endl;

        // Tags
        for(const auto & tag : problem.getAllTags()) {

            ostream << "(declare-fun t_" << id << "_tag_" << tag << " () Int)" << std::endl;
            ostream << "(assert (= t_" << id << "_tag_" << tag << " " << ts.getTagPriority(tag) << "))" << std::endl;

        }

        // Groups
        for(const auto & group : problem.getAllGroups()) {

            ostream << "(declare-fun t_" << id << "_group_" << group << " () Bool)" << std::endl;

            if(ts.inGroup(group))
                ostream << "(assert t_" << id << "_group_" << group << ")" << std::endl;
            else
                ostream << "(assert (not t_" << id << "_group_" << group << "))" << std::endl;
        }

    }

    for(const auto & [id, task] : problem.getAllTasks()) {

        ostream << "(declare-fun a_" << id  << "_start () Int)      ; new task" << std::endl;
        ostream << "(declare-fun a_" << id << "_duration () Int)" << std::endl;
        ostream << "(declare-fun a_" << id << "_deadline () Int)" << std::endl;
        ostream << "(declare-fun a_" << id << "_optional() Bool)" << std::endl;

        // Tags
        for(const auto & tag : problem.getAllTags()) {

            ostream << "(declare-fun a_" << id << "_tag_" << tag << " () Int)" << std::endl;
            ostream << "(assert (= a_" << id << "_tag_" << tag << " " << task.getTagPriority(tag) << "))" << std::endl;

        }

        // Groups
        for(const auto & group : problem.getAllGroups()) {

            ostream << "(declare-fun a_" << id << "_group_" << group << " () Bool)" << std::endl;

            if(task.inGroup(group))
                ostream << "(assert a_" << id << "_group_" << group << ")" << std::endl;
            else
                ostream << "(assert (not a_" << id << "_group_" << group << "))" << std::endl;

        }


    }

    // Assignment constraints
    // Add an "assigned" variable for all
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            ostream << "(declare-fun assign_" << tsid << "_" << aid << " () Bool)" << std::endl;

    // 0. a timeslot cannot be double-booked
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            for(const auto &[aid2, action2] : problem.getAllTasks())
                if(aid != aid2)
                    ostream << "(assert (=> " << assignID(tsid, aid) << " (not " << "assign_" << tsid << "_" << aid2 << ")))" << std::endl;


    // 1. task cannot be scheduled before its start point
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            ostream << "(assert (=> " << assignID(tsid, aid) <<
                    " (<= "
                    << "(+ " << timeBetween(unit, start, action.getStartPoint()) << " " << timeInUnit(unit, action.getDuration()) << ")"
                    << "(+ " << timeBetween(unit, start, ts.getStartPoint()) << " " << timeInUnit(unit, ts.getDuration()) << ")"
                    << ")))" << std::endl;


    // 2. Task execution cannot exceed its deadline


    // 3. Task duration cannot exceed timeslot duration


    // 4.


    ostream << "(check-sat)" << std::endl;

    ostream.close();

}


