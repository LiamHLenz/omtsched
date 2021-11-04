//
// Created by dana on 11.05.21.
//

#ifndef OMTSCHED_TRANSLATOR_Z3HPP
#define OMTSCHED_TRANSLATOR_Z3HPP


#include "../z3/TranslatorZ3.h"


/*

template <typename TaskID, typename TimeslotID, typename ID, typename ID>
bool TranslatorZ3<TaskID, TimeslotID, ID, ID>::solve(const Problem<TaskID, TimeslotID, ID, ID> &problem) {

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
        task_expr[id].push_back(start);

        auto duration = context.int_const( ("ad" + std::to_string(acount)).c_str() );    // Duration
        task_expr[id].push_back(duration);

        auto deadline = context.int_const( ("adl" + std::to_string(acount)).c_str() );   // Deadline
        task_expr[id].push_back(deadline);

        auto optional = context.bool_const( ("as" + std::to_string(acount)).c_str() );   // Optional
        task_expr[id].push_back(optional);

        // Tags
        for(const auto & [tag, ID] : tag_id) {

            auto tagexpr = context.int_const( ("a" + std::to_string(acount) + "t" + std::to_string(ID)).c_str() );
            task_tags.set(id, tag, tagexpr);

        }

        // Groups
        for(const auto & [group, gid] : group_id) {

            auto groupexpr = context.bool_const( ("a" + std::to_string(acount) + "g" + std::to_string(gid)).c_str() );
            task_groups.set(id, group, groupexpr);

        }

        acount++;
    }


    // Declare all timeslot-related constants
    size_t tcount = 0;
    for(const auto & [id, ts] : problem.getAllTimeslots()) {

        // Assign an internal numerical ID
        ts_id[id] = tcount;

        auto start = context.int_const( ("ts" + std::to_string(tcount)).c_str() );       // Start Point
        ts_expr[id].push_back(start);

        auto duration = context.int_const( ("td" + std::to_string(tcount)).c_str() );    // Duration
        ts_expr[id].push_back(duration);

        // Tags
        for(const auto & [tag, ID] : tag_id) {

            auto tagexpr = context.int_const( ("t" + std::to_string(tcount) + "t" + std::to_string(ID)).c_str() );
            ts_tags.set(id, tag, tagexpr);

        }

        // Groups
        for(const auto & [group, gid] : group_id) {

            auto groupexpr = context.bool_const( ("t" + std::to_string(tcount) + "g" + std::to_string(gid)).c_str() );
            ts_groups.set(id, group, groupexpr);

        }

        tcount++;
    }


    // Declare all assignment-variables
    for(const auto &[tid, tiid] : ts_id)
        for(const auto &[aid, aiid] : task_id) {
            assign_expr.set(tid, aid, context.bool_const( tiid + "-" + aiid));
        }


    // --------- Initiate solver ----------

    z3::solver solver(context);

    // ----- Pick variables represented in unsat-core -----

    z3::expr_vector core_vars {context};

    for(const auto &assign : task_expr)
        core_vars.push_back(assign.second.at(0));


    //---------------------------------------------------------------------------------------
    // ---------------------- Assert given values of all constants --------------------------
    //---------------------------------------------------------------------------------------

    auto startPoint = problem.getStartPoint();
    auto unit = problem.getUnit();

    /*
    // Assert task-related values
    for(const auto & [id, task] : problem.getAllTasks()) {

        const auto & internal_id = task_id.at(id);

        const auto &start = task_expr[id][Attributes::Start];                       // Start Point
        solver.add( start == timeBetween(unit, startPoint, task.getStartPoint()) );

        const auto &duration = task_expr[id][Attributes::Duration];                 // Duration
        solver.add( duration == timeInUnit(unit, task.getDuration()) );

        const auto &deadline = task_expr[id][Attributes::Deadline];                 // Deadline
        solver.add( deadline == timeBetween(unit, startPoint, task.getDeadline()) );

        const auto &optional = task_expr[id][Attributes::Optional];                 // Optional

        if(task.isOptional())
            solver.add( optional );
        else
            solver.add( !optional );


        // Tags
        for(const auto &tag : problem.getAllTags()) {

            const auto &tagexpr = task_tags.get(id, tag);
            solver.add( tagexpr == task.getTagPriority(tag) );

        }


        // Groups
        for(const auto &group : problem.getAllGroups()) {

            const auto &groupexpr = task_groups.get(id, group);

            if (task.inGroup(group))
                solver.add( groupexpr );
            else
                solver.add( !groupexpr );
        }
    }


    // Assert timeslot-related values
    for(const auto & [id, timeslot] : problem.getAllTimeslots()) {

        const auto & internal_id = ts_id.at(id);

        const auto &start = ts_expr[id][Attributes::Start];                       // Start Point
        solver.add( start == timeBetween(unit, startPoint, timeslot.getStartPoint()) );

        const auto &duration = ts_expr[id][Attributes::Duration];                 // Duration
        solver.add( duration == timeInUnit(unit, timeslot.getDuration()) );


        // Tags
        for(const auto &tag : problem.getAllTags()) {

            const auto &tagexpr = ts_tags.get(id, tag);
            solver.add( tagexpr == timeslot.getTagPriority(tag) );

        }


        // Groups
        for(const auto &group : problem.getAllGroups()) {

            const auto &groupexpr = ts_groups.get(id, group);

            if (timeslot.inGroup(group))
                solver.add( groupexpr );
            else
                solver.add( !groupexpr );
        }
    }*/

/*
    //---------------------------------------------------------------------------------------
    // ------------------------- Assert rules for assignments -------------------------------
    //---------------------------------------------------------------------------------------



    for(const auto &[tid, timeslot] : problem.getAllTimeslots())
        for(const auto &[aid, task] : problem.getAllTasks()) {

            const auto &assigned = assign_expr.get(tid, aid);

            // C1 a timeslot cannot be double-booked
            for (const auto &[aid2, task] : problem.getAllTasks())
                if (aid != aid2) {


                    const auto &assigned2 = assign_expr.get(tid, aid2);
                    solver.add(!assigned || !assigned2);

                }

            // C2 a task cannot be double-assigned
            for (const auto &[tid2, timeslot] : problem.getAllTimeslots())
                if (tid != tid2) {

                    const z3::expr &assigned1 = assign_expr.get(tid, aid);
                    const z3::expr &assigned2 = assign_expr.get(tid2, aid);
                    solver.add(!assigned || !assigned2);

                }

            // C3 task cannot be scheduled before its start point
            if(timeslot.getStartPoint() < task.getStartpoint)
                solver.add( !assigned, "ts before task start" );

            // C4 Task execution cannot exceed its deadline
            if(timeslot.getStartPoint() + task.getDuration() > task.getDeadline())
                solver.add( !assigned, "Would violate deadline");

            // C5 Task duration cannot exceed timeslot duration
            if(timeslot.getDuration() < task.getDuration())
                solver.add( !assigned, "TS too small");

            // C6 If a tag is set on a task, it must be set on a timeslot
            for(const auto &tag : problem.getAllTags())
                if( task.getTagPriority(tag) > 0 && timeslot.getTagPriority(tag) == 0 )
                    solver.add( !assigned, "Tag Conflict");

        }

    // C7 All non-optional tasks need to be assigned
    for(const auto &[aid, task] : problem.getAllTasks())
        if(!task.isOptional()) {


            auto expr = get_assigned_expr(aid);

            solver.add(expr);
        }


    //---------------------------------------------------------------------------------------
    // --------------------------- Assert given constraints ---------------------------------
    //---------------------------------------------------------------------------------------

    for(const auto &constraint : problem.getConstraints()) {

        switch (constraint.type) {

            case ConstraintType::BIND :

                solver.add( assign_expr.get(constraint.ts, constraint.task) );
                break;

            case ConstraintType::X_OF :

                break;

            case ConstraintType::AT_LEAST :

                break;

            case ConstraintType::AT_MOST :

                break;

        }

    }


    // ------ Pass to Z3 and solve ---------

    auto result = solver.check(context);

    std::cout << result << std::endl;

    switch(result) {

        case z3::check_result::sat :
            std::cout << solver.get_model() << std::endl;
            return true;

        case z3::check_result::unsat :
            //for(const auto &expr : solver.unsat_core() )
            //    std::cout << expr << std::endl;
            //std::cout << solver.unsat_core() << std::endl;
            return false;

        case z3::check_result::unknown :
            break;
    }

    return true;
}

template<typename Key1, typename Key2>
const z3::expr expr_map<Key1, Key2>::get(const Key1 &key1, const Key2 &key2) const {

    return internal_map.at({key1, key2}).at(0);
}

template<typename Key1, typename Key2>
void expr_map<Key1, Key2>::set(const Key1 &key1, const Key2 &key2, z3::expr expr) {

    internal_map[{key1, key2}].push_back(expr);
}
*/

#endif //OMTSCHED_TRANSLATOR_Z3HPP
