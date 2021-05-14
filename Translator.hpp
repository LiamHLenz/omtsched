//
// Created by dana on 11.05.21.
//

#ifndef OMTSCHED_TRANSLATOR_HPP
#define OMTSCHED_TRANSLATOR_HPP


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
    ostream << "(set-option :produce-models true)" << std::endl;

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


    // 3. Task duration cannot exceed timeslot duration


    // 4.


    ostream << "(check-sat)" << std::endl;
    ostream << "(get-value (";

    for(const auto &[t, tid] : ts_id)
        for(const auto &[a, aid] : task_id)
            ostream << assigned(tid, aid) << " ";

    ostream << "))" << std::endl;

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

/*
template <typename TaskID, typename TimeslotID, typename GroupID, typename TagID>
bool Translator<TaskID, TimeslotID, GroupID, TagID>::solveZ3(const Problem<TaskID, TimeslotID, GroupID, TagID> problem) {

    using namespace z3;

    enum {
        ID = 0, Start = 1, Duration = 2, Deadline = 3, Optional = 4
    };


    // Set up internal data structures
    // TODO: setup in a different function
    const size_t num_tasks = problem.getAllTasks().size();
    const size_t num_timeslots = problem.getAllTimeslots().size();
    const size_t num_tags = problem.getAllTags().size();
    const size_t num_groups = problem.getAllGroups().size();

    size_t t = 0;
    for(const auto tag : problem.getAllTags())
        tag_id[tag] = t++;

    size_t g = 0;
    for(const auto group : problem.getAllGroups())
        group_id[group] = g++;


    // Declare all variables

    context c;

    size_t tid = 0;

    for(const auto & [id, ts] : problem.getAllTimeslots()) {

        const std::string t = "t";

        ts_id[id] = tid;
        c.int_const(makeID(t, tid, "s"));
        c.int_const(makeID(t, tid, "d"));

        // Tags
        for(const auto & [tagid, zid] : tag_id)
            c.int_const(makeID(t, tid, "t", zid));

        // Groups
        for(const auto & [groupid, zid] : group_id)
            c.bool_const(makeID(t, tid, "t", zid));

        tid++;
    }

    size_t aid = 0;

    for(const auto & [id, action] : problem.getAllTasks()) {

        const std::string a = "a";

        task_id[id] = aid;
        c.int_const(makeID(a, aid, "s"));
        c.int_const(makeID(a, aid, "du"));
        c.int_const(makeID(a, aid, "dl"));
        c.bool_const(makeID(a, aid, "o"));

        // Tags
        for(const auto & [tagid, zid] : tag_id)
            c.int_const(makeID(a, aid, "t", zid));

        // Groups
        for(const auto & [groupid, zid] : group_id)
            c.bool_const(makeID(a, aid, "g", zid));

        aid++;
    }

    // Declare assignment variables
    for(size_t ti = 0; ti < num_timeslots; ti++)
        for(size_t ai = 0; ai < num_tasks; ai++)
            c.bool_const(makeID(ti, "assign", ai));



    // Assert: given values
    auto start_point = problem.getStartPoint();
    auto unit = problem.getUnit();
    auto s = solver(c);

    // Assert existing values for timeslots
    for(const auto & [id, ts] : problem.getAllTimeslots()) {


        auto &tid = ts_id.at(id);

        auto &start = makeID(t, tid, "s");
        s.add(start == timeBetween(unit, start_point, ts.getStartPoint()));

        auto &duration = makeID(t, tid, "d");
        s.add(duration == timeInUnit(unit, ts.getDuration()));


        // Tags
        for(const auto & tag : problem.getAllTags())
            s.add(makeID(t, tid, "t", tag_id.at(tag)) == ts.getTagPriority(tag));

        // Groups
        for(const auto & group : problem.getAllGroups())
            if(ts.inGroup(group))
                s.add(makeID(t, tid, "g", group_id.at(group)));
            else
                s.add(!makeID(t, tid, "g", group_id.at(group)));

    }


    // Assert values for tasks

    for(const auto & [id, task] : problem.getAllTasks()) {

        const std::string a = "a";
        const auto &aid = task_id.at(id);

        const auto &start = makeID(a, aid, "s");
        s.add(start == timeBetween(unit, start_point, task.getStartPoint()));

        const auto &duration = makeID(a, aid, "du");
        s.add(duration == timeInUnit(unit, task.getDuration()));

        const auto &deadline =makeID(a, aid, "dl");
        s.add(deadline == timeBetween(unit, start_point, task.getDeadlinePoint()));

        const auto &optional =makeID(a, aid, "o");

        if(task.isOptional())
            s.add(optional);
        else
            s.add(!optional);

        // Tags
        for(const auto & tag : problem.getAllTags())
            s.add(makeID(a, aid, "t", tag_id.at(tag)) == task.getTagPriority(tag));

        // Groups
        for(const auto & group : problem.getAllGroups())
            if(task.inGroup(group))
                s.add(makeID(a, aid, "g", group_id.at(group)));
            else
                s.add(!makeID(t, tid, "g", group_id.at(group)));

    }


    // Assignment constraints

    // 0. a timeslot cannot be double-booked
    for(const auto &[tsid, tzid] : ts_id)
        for(const auto &[aid, azid] : task_id)
            for(const auto &[aid2, azid2] : task_id)
                if(azid != azid2)
                    s.add( !makeID(tzid, "assign", azid) || !makeID(tzid, "assign", azid2));


    // 1. task cannot be scheduled before its start point
    for(const auto &[tid, ts] : problem.getAllTimeslots())
        for(const auto &[aid, task] : problem.getAllTasks()) {

            const auto &tzid = ts_id.at(tid);
            const auto &azid = task_id.at(aid);

            const auto assign = makeID(tzid, "assign", azid);

            const auto taskStart = makeID();
            const auto aStart = timeBetween(unit, start_point, task.getStartPoint());

            z3::expr tStartExpr;
            const auto tStart = timeBetween(unit, start_point, ts.getStartPoint());

        }


    // 2. Task execution cannot exceed its deadline


    // 3. Task duration cannot exceed timeslot duration


    // 4.

    std::cout << s.check();

} */


#endif //OMTSCHED_TRANSLATOR_HPP
