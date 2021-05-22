//
// Created by dana on 11.05.21.
//

#ifndef OMTSCHED_TRANSLATOR_HPP
#define OMTSCHED_TRANSLATOR_HPP


#include "Translator.h"

template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
bool Translator<TaskID, TimeslotID, GroupID, TagID>::solve(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem, const Solver &solver) {

    switch (solver) {

        case Solver::Z3 :
            return solveZ3(problem);

    }

}


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
int Translator<TaskID, TimeslotID, GroupID, TagID>::timeInUnit(const Unit &unit, const boost::posix_time::time_duration &duration) const {

    switch (unit) {

        case Unit::HOURS:
            return duration.hours();

        case Unit::MINUTES:
            return duration.hours() *60 + duration.minutes();

        case Unit::SECONDS:
            return duration.hours()*60*60 + duration.minutes()*60 + duration.seconds();


    }

}

template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
int Translator<TaskID, TimeslotID, GroupID, TagID>::timeBetween(const Unit &unit, const boost::posix_time::ptime &first, const boost::posix_time::ptime &second) const {

    boost::posix_time::time_duration between = second - first;

    return timeInUnit(unit, between);

}


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const std::string Translator<TaskID, TimeslotID, GroupID, TagID>::assigned(const size_t &tid, const size_t &aid) const {

    return "c" + std::to_string(tid) + "_" + std::to_string(aid);

}


template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
void Translator<TaskID, TimeslotID, GroupID, TagID>::saveEncoding(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem) {

    std::ofstream ostream(problem.problemName + ".smt2");

    ostream << "(set-logic QF_LIA)" << std::endl;
    //ostream << "(set-option :produce-models true)" << std::endl;
    //ostream << "(set-option :produce-unsat-cores true)" << std::endl;

    //---------------------------------------------------------------------------------------
    // ---------------------- Declare all used variables/constants --------------------------
    //---------------------------------------------------------------------------------------


    // Assign internal numerical IDs to all tags and groups
    size_t tag_count = 0;
    for(const auto & tag : problem.getAllTags())
        tag_id[tag] = tag_count++;

    size_t group_count = 0;
    for(const auto & group : problem.getAllGroups())
        group_id[group] = group_count++;


    // Declare all task-related constants
    size_t acount = 0;
    for(const auto & [id, task] : problem.getAllTasks()) {

        // Assign an internal numerical ID
        task_id[id] = acount;

        ostream << "(declare-fun a" << acount  << "s () Int)      ; new task" << std::endl; // Start Point
        ostream << "(declare-fun a" << acount << "du () Int)" << std::endl;                 // Duration
        ostream << "(declare-fun a" << acount << "dl () Int)" << std::endl;                 // Deadline
        ostream << "(declare-fun a" << acount << "o () Bool)" << std::endl;                 // Optional

        // Tags
        for(const auto & [tag, tagid] : tag_id)
            ostream << "(declare-fun a" << acount << "t" << tagid << " () Int)" << std::endl;

        // Groups
        for(const auto & [group, gid] : group_id)
            ostream << "(declare-fun a" << acount << "g" << gid << " () Bool)" << std::endl;

        acount++;
    }


    // Declare all timeslot-related constants
    size_t tcount = 0;
    for(const auto & [id, ts] : problem.getAllTimeslots()) {

        // Assign an internal numerical ID
        ts_id[id] = tcount;

        ostream << "(declare-fun t" << tcount  << "s () Int)      ; new task" << std::endl; // Start Point
        ostream << "(declare-fun t" << tcount << "du () Int)" << std::endl;                 // Duration

        // Tags
        for(const auto & [tag, tagid] : tag_id)
            ostream << "(declare-fun t" << tcount << "t" << tagid << " () Int)" << std::endl;

        // Groups
        for(const auto & [group, gid] : group_id)
            ostream << "(declare-fun t" << tcount << "g" << gid << " () Bool)" << std::endl;

        tcount++;
    }


    // Declare all assignment-variables
    for(const auto &[tid, tzid] : ts_id)
        for(const auto &[aid, azid] : task_id)
            ostream << "(declare-fun " << assigned(tzid, azid) << " () Bool)" << std::endl;



    //---------------------------------------------------------------------------------------
    // ---------------------- Assert given values of all constants --------------------------
    //---------------------------------------------------------------------------------------

    auto startPoint = problem.getStartPoint();
    auto unit = problem.getUnit();

    // Assert task-related values
    for(const auto & [id, task] : problem.getAllTasks()) {

        const auto & internal_id = task_id.at(id);

        ostream << "(assert (= a" << internal_id << "s " << timeBetween(unit, startPoint, task.getStartPoint()) << "))" << std::endl; // Start Point
        ostream << "(assert (= a" << internal_id << "du " << timeInUnit(unit, task.getDuration()) << "))" << std::endl;             // Duration
        ostream << "(assert (= a" << internal_id << "dl " << timeBetween(unit, startPoint, task.getDeadline()) << "))" << std::endl;  // Deadline

        // Optionality
        if(task.isOptional())
            ostream << "(assert a" << internal_id << "o)" << std::endl;
        else
            ostream << "(assert (not a" << internal_id << "o))" << std::endl;


        // Tags
        for(const auto & [tag, tagid] : tag_id)
            ostream << "(assert (= a" << internal_id << "t" << tagid << " " << task.getTagPriority(tag) << "))" << std::endl;


        // Groups
        for(const auto & [group, groupid] : group_id)

            if(task.inGroup(group))
                ostream << "(assert a" << internal_id << "g" << groupid << ")" << std::endl;
            else
                ostream << "(assert (not a" << internal_id << "g" << groupid << "))" << std::endl;
    }


    // Assert timeslot-related values
    for(const auto & [id, timeslot] : problem.getAllTimeslots()) {

        const auto & internal_id = ts_id.at(id);

        ostream << "(assert (= t" << internal_id << "s " << timeBetween(unit, startPoint, timeslot.getStartPoint()) << "))" << std::endl; // Start Point
        ostream << "(assert (= t" << internal_id << "du " << timeInUnit(unit, timeslot.getDuration()) << "))" << std::endl;             // Duration


        // Tags
        for(const auto & [tag, tagid] : tag_id)
            ostream << "(assert (= t" << internal_id << "t" << tagid << " " << timeslot.getTagPriority(tag) << "))" << std::endl;

        // Groups
        for(const auto & [group, groupid] : group_id)

            if(timeslot.inGroup(group))
                ostream << "(assert t" << internal_id << "g" << groupid << ")" << std::endl;
            else
                ostream << "(assert (not t" << internal_id << "g" << groupid << "))" << std::endl;
    }


    //---------------------------------------------------------------------------------------
    // ---------------------- Assert constraints for assignments ----------------------------
    //---------------------------------------------------------------------------------------


    // 0. a timeslot cannot be double-booked
    for(const auto &[tid, tiid] : ts_id)
        for(const auto &[aid, aiid] : task_id)
            for(const auto &[aid2, aiid2] : task_id)
                if(aiid != aiid2)
                    ostream << "(assert (or (not " << assigned(tiid, aiid) << ") (not " << assigned(tiid, aiid2) << ")))" << std::endl;


    // 1. task cannot be scheduled before its start point
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            ostream << "(assert (=> " << assigned(ts_id.at(tsid), task_id.at(aid))
                    << " (>= " << timeBetween(unit, startPoint, action.getStartPoint())
                    << " " << timeBetween(unit, startPoint, ts.getStartPoint()) << ")))" << std::endl;


    // 2. Task execution cannot exceed its deadline
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            ostream << "(assert (=> " << assigned(ts_id.at(tsid), task_id.at(aid))
                    << " (<= " << timeBetween(unit, startPoint, ts.getStartPoint()) + timeInUnit(unit, ts.getDuration())
                    << " " << timeBetween(unit, startPoint, action.getDeadline()) << ")))" << std::endl;


    // 3. Task duration cannot exceed timeslot duration
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            ostream << "(assert (=> " << assigned(ts_id.at(tsid), task_id.at(aid))
                    << "(<= " << timeInUnit(unit, action.getDuration())
                    << " " << timeInUnit(unit, ts.getDuration()) << ")))" << std::endl;


    // 4. If a tag is set on a task, it must be set on a timeslot
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks()) {
            ostream << "(assert (! (=> " << assigned(ts_id.at(tsid), task_id.at(aid))
                    << " (and ";
            for(const auto &tag : problem.getAllTags())
                ostream << "(=> (< 0 " << action.getTagPriority(tag) << ") (< 0 " << ts.getTagPriority(tag) << ")) ";

            ostream << ")) :named tags-" << tsid << "-" << aid << "))" << std::endl;
        }


    // 5. All non-optional tasks need to be assigned

    for(const auto &[aid, action] : problem.getAllTasks())
        if(!action.isOptional()) {

            ostream << "(assert (! (or ";

            for(const auto &[tsid, ts] : problem.getAllTimeslots())
                ostream << assigned(ts_id.at(tsid), task_id.at(aid)) << " ";

            ostream << ") :named assign-" << aid << "))" << std::endl;
        }


    //---------------------------------------------------------------------------------------
    // -------------------------------- Final Settings --------------------------------------
    //---------------------------------------------------------------------------------------


    ostream << "(check-sat)" << std::endl;
    /*ostream << "(get-value (";

    for(const auto &[t, tid] : ts_id)
        for(const auto &[a, aid] : task_id)
            ostream << assigned(tid, aid) << " ";
*/
    //ostream << "(get-unsat-core)" << std::endl;

    //ostream << "))" << std::endl;

    ostream.close();

}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const char* Translator<TaskID, TimeslotID, GroupID, TagID>::makeID(const std::string &type, const size_t &number, const std::string &attribute) const {

    return (type + std::to_string(number) + attribute).c_str();

}

template<typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
const char* Translator<TaskID, TimeslotID, GroupID, TagID>::makeID(const std::string &type, const size_t &num1, const std::string &attribute, const size_t &num2) const {

    return (type + std::to_string(num1) + attribute + std::to_string(num2)).c_str();

}


template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
bool Translator<TaskID, TimeslotID, GroupID, TagID>::solveZ3(const Problem<TaskID, TimeslotID, GroupID, TagID> &problem) {

    saveEncoding(problem);

    z3::context context;

    //---------------------------------------------------------------------------------------
    // ---------------------- Declare all used variables/constants --------------------------
    //---------------------------------------------------------------------------------------


    // Assign internal numerical IDs to all tags and groups
    size_t tag_count = 0;
    for(const auto & tag : problem.getAllTags())
        tag_id[tag] = tag_count++;

    size_t group_count = 0;
    for(const auto & group : problem.getAllGroups())
        group_id[group] = group_count++;


    // Declare all task-related constants
    size_t acount = 0;
    for(const auto & [id, task] : problem.getAllTasks()) {

        // Assign an internal numerical ID
        task_id[id] = acount;

        auto start = context.int_const( ("as" + std::to_string(acount)).c_str() );       // Start Point
        task_expr[id][TaskAttributes::Start] = start;

        auto duration = context.int_const( ("ad" + std::to_string(acount)).c_str() );    // Duration
        task_expr[id][TaskAttributes::Duration] = duration;

        auto deadline = context.int_const( ("adl" + std::to_string(acount)).c_str() );   // Deadline
        task_expr[id][TaskAttributes::Deadline] = deadline;

        auto optional = context.bool_const( ("as" + std::to_string(acount)).c_str() );   // Optional
        task_expr[id][TaskAttributes::Optional] = optional;

        // Tags
        for(const auto & [tag, tagid] : tag_id) {

            auto tagexpr = context.int_const( ("a" + std::to_string(acount) + "t" + tagid).c_str() );
            task_tags[id][tag] = tagexpr;

        }

        // Groups
        for(const auto & [group, gid] : group_id) {

            auto groupexpr = context.bool_const( ("a" + std::to_string(acount) + "g" + gid).c_str() );
            task_tags[id][group] = groupexpr;

        }

        acount++;
    }


    // Declare all timeslot-related constants
    size_t tcount = 0;
    for(const auto & [id, ts] : problem.getAllTimeslots()) {

        // Assign an internal numerical ID
        ts_id[id] = tcount;

        auto start = context.int_const( ("ts" + std::to_string(tcount)).c_str() );       // Start Point
        task_expr[id][TSAttributes::Start] = start;

        auto duration = context.int_const( ("td" + std::to_string(tcount)).c_str() );    // Duration
        task_expr[id][TSAttributes::Duration] = duration;

        // Tags
        for(const auto & [tag, tagid] : tag_id) {

            auto tagexpr = context.int_const( ("t" + std::to_string(tcount) + "t" + tagid).c_str() );
            task_tags[id][tag] = tagexpr;

        }

        // Groups
        for(const auto & [group, gid] : group_id) {

            auto groupexpr = context.bool_const( ("t" + std::to_string(tcount) + "g" + gid).c_str() );
            task_tags[id][group] = groupexpr;

        }

        tcount++;
    }


    // Declare all assignment-variables
    for(const auto &[tid, tzid] : ts_id)
        for(const auto &[aid, azid] : task_id) {

            auto assign = context.bool_const( tzid + "-" + azid );
            assign_expr({tzid, azid}, assign);

        }



    //---------------------------------------------------------------------------------------
    // ---------------------- Assert given values of all constants --------------------------
    //---------------------------------------------------------------------------------------

    auto startPoint = problem.getStartPoint();
    auto unit = problem.getUnit();

    // Assert task-related values
    for(const auto & [id, task] : problem.getAllTasks()) {

        const auto & internal_id = task_id.at(id);

        ostream << "(assert (= a" << internal_id << "s " << timeBetween(unit, startPoint, task.getStartPoint()) << "))" << std::endl; // Start Point
        ostream << "(assert (= a" << internal_id << "du " << timeInUnit(unit, task.getDuration()) << "))" << std::endl;             // Duration
        ostream << "(assert (= a" << internal_id << "dl " << timeBetween(unit, startPoint, task.getDeadline()) << "))" << std::endl;  // Deadline

        // Optionality
        if(task.isOptional())
            ostream << "(assert a" << internal_id << "o)" << std::endl;
        else
            ostream << "(assert (not a" << internal_id << "o))" << std::endl;


        // Tags
        for(const auto & [tag, tagid] : tag_id)
            ostream << "(assert (= a" << internal_id << "t" << tagid << " " << task.getTagPriority(tag) << "))" << std::endl;


        // Groups
        for(const auto & [group, groupid] : group_id)

            if(task.inGroup(group))
                ostream << "(assert a" << internal_id << "g" << groupid << ")" << std::endl;
            else
                ostream << "(assert (not a" << internal_id << "g" << groupid << "))" << std::endl;
    }


    // Assert timeslot-related values
    for(const auto & [id, timeslot] : problem.getAllTimeslots()) {

        const auto & internal_id = ts_id.at(id);

        ostream << "(assert (= t" << internal_id << "s " << timeBetween(unit, startPoint, timeslot.getStartPoint()) << "))" << std::endl; // Start Point
        ostream << "(assert (= t" << internal_id << "du " << timeInUnit(unit, timeslot.getDuration()) << "))" << std::endl;             // Duration


        // Tags
        for(const auto & [tag, tagid] : tag_id)
            ostream << "(assert (= t" << internal_id << "t" << tagid << " " << timeslot.getTagPriority(tag) << "))" << std::endl;

        // Groups
        for(const auto & [group, groupid] : group_id)

            if(timeslot.inGroup(group))
                ostream << "(assert t" << internal_id << "g" << groupid << ")" << std::endl;
            else
                ostream << "(assert (not t" << internal_id << "g" << groupid << "))" << std::endl;
    }


    //---------------------------------------------------------------------------------------
    // ---------------------- Assert constraints for assignments ----------------------------
    //---------------------------------------------------------------------------------------


    // 0. a timeslot cannot be double-booked
    for(const auto &[tid, tiid] : ts_id)
        for(const auto &[aid, aiid] : task_id)
            for(const auto &[aid2, aiid2] : task_id)
                if(aiid != aiid2)
                    ostream << "(assert (or (not " << assigned(tiid, aiid) << ") (not " << assigned(tiid, aiid2) << ")))" << std::endl;


    // 1. task cannot be scheduled before its start point
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            ostream << "(assert (=> " << assigned(ts_id.at(tsid), task_id.at(aid))
                    << " (>= " << timeBetween(unit, startPoint, action.getStartPoint())
                    << " " << timeBetween(unit, startPoint, ts.getStartPoint()) << ")))" << std::endl;


    // 2. Task execution cannot exceed its deadline
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            ostream << "(assert (=> " << assigned(ts_id.at(tsid), task_id.at(aid))
                    << " (<= " << timeBetween(unit, startPoint, ts.getStartPoint()) + timeInUnit(unit, ts.getDuration())
                    << " " << timeBetween(unit, startPoint, action.getDeadline()) << ")))" << std::endl;


    // 3. Task duration cannot exceed timeslot duration
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks())
            ostream << "(assert (=> " << assigned(ts_id.at(tsid), task_id.at(aid))
                    << "(<= " << timeInUnit(unit, action.getDuration())
                    << " " << timeInUnit(unit, ts.getDuration()) << ")))" << std::endl;


    // 4. If a tag is set on a task, it must be set on a timeslot
    for(const auto &[tsid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, action] : problem.getAllTasks()) {
            ostream << "(assert (! (=> " << assigned(ts_id.at(tsid), task_id.at(aid))
                    << " (and ";
            for(const auto &tag : problem.getAllTags())
                ostream << "(=> (< 0 " << action.getTagPriority(tag) << ") (< 0 " << ts.getTagPriority(tag) << ")) ";

            ostream << ")) :named tags-" << tsid << "-" << aid << "))" << std::endl;
        }


    // 5. All non-optional tasks need to be assigned

    for(const auto &[aid, action] : problem.getAllTasks())
        if(!action.isOptional()) {

            ostream << "(assert (! (or ";

            for(const auto &[tsid, ts] : problem.getAllTimeslots())
                ostream << assigned(ts_id.at(tsid), task_id.at(aid)) << " ";

            ostream << ") :named assign-" << aid << "))" << std::endl;
        }



    // ------ Pass to Z3 and solve ---------

    z3::solver solver(context);

    auto result = solver.check();

    std::cout << result << std::endl;

    switch(result) {

        case z3::check_result::sat :
            std::cout << solver.get_model() << std::endl;
            return true;

        case z3::check_result::unsat :
            std::cout << solver.unsat_core() << std::endl;
            return false;

        case z3::check_result::unknown :
            break;
    }

    return true;
}


#endif //OMTSCHED_TRANSLATOR_HPP
