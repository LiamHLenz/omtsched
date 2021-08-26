//
// Created by dana on 16.05.21.
//

#include "../omtsched.h"
#include "problems.h"

//template <typename ... Groups>
void addLecture(Problem<std::string, std::string, std::string, std::string> &problem, boost::posix_time::ptime startTime, boost::gregorian::date endDate, std::initializer_list<std::string> groups) {

    using namespace boost::gregorian;
    using namespace boost::posix_time;

    for(week_iterator date = startTime.date(); date < startTime.date() + weeks(1); ++date) {
//    for(week_iterator date = startTime.date(); date <= endDate; ++date) {


        // Construct a unique and understandable name
        std::string title;
        for(auto it = groups.begin(); it != groups.end(); it++)
            title.append(*it).append("_");

        title.append(boost::gregorian::to_iso_string(*date));

        ptime start {*date, startTime.time_of_day()};

        time_duration duration {minutes(120)};
        auto &task = problem.addTask(title, start, duration, start + duration, false);
        auto &ts = problem.addTimeslot(to_iso_string(start), start, duration);

        task.addGroup("Uni");

        for(auto it = groups.begin(); it != groups.end(); it++)
            task.addGroup(*it);

        problem.bind(ts.getID(), task.getTaskId());

    }

}

void addHomework(Problem<std::string, std::string, std::string, std::string> &problem, boost::posix_time::ptime startTime, boost::gregorian::date endDate, std::initializer_list<std::string> groups) {

    // Estimating 3 hours per subject per homework
    using namespace boost::gregorian;
    using namespace boost::posix_time;

    for(week_iterator date = startTime.date(); date < startTime.date() + weeks(1); ++date) {
//    for(week_iterator date = startTime.date(); date <= endDate; ++date) {


        // Construct a unique and understandable name
        std::string title = "Homework";
        for(auto it = groups.begin(); it != groups.end(); it++)
            title.append(*it).append("_");

        title.append(boost::gregorian::to_iso_string(*date));

        ptime start {*date, startTime.time_of_day()};

        time_duration duration {minutes(180)};
        auto &task = problem.addTask(title, start, duration, start + weeks(1), false);

        task.addGroup("Uni");
        task.addGroup("Homework");

        for(auto it = groups.begin(); it != groups.end(); it++)
            task.addGroup(*it);

        task.setTagPriority("Focus", 3);
    }

}

void addReview(Problem<std::string, std::string, std::string, std::string> &problem, boost::posix_time::ptime startTime, boost::gregorian::date endDate, std::initializer_list<std::string> groups) {

    using namespace boost::gregorian;
    using namespace boost::posix_time;

//    for(week_iterator date = startTime.date(); date < startTime.date() + weeks(1); ++date) {
    for(week_iterator date = startTime.date(); date <= endDate; ++date) {

        // Construct a unique and understandable name
        std::string title = "Review1";
        for (auto it = groups.begin(); it != groups.end(); it++)
            title.append(*it).append("_");

        title.append(boost::gregorian::to_iso_string(*date));

        ptime start{*date, startTime.time_of_day()};

        time_duration duration{minutes(60)};
        auto &task = problem.addTask(title, start, duration, start + weeks(1), true);

        task.addGroup("Uni");
        task.addGroup("Review");

        for (auto it = groups.begin(); it != groups.end(); it++)
            task.addGroup(*it);

        task.setTagPriority("Focus", 2);
    }

}

void addStudyTime(Problem<std::string, std::string, std::string, std::string> &problem,  boost::posix_time::ptime startTime, boost::gregorian::date endDate, std::initializer_list<std::string> tags) {

    using namespace boost::gregorian;
    using namespace boost::posix_time;

    for(week_iterator date = startTime.date(); date <= endDate; ++date) {

        // Construct a unique and understandable name
        std::string title = "Study_";

        title.append(boost::gregorian::to_iso_string(*date));
        title.append(boost::posix_time::to_iso_string(startTime.time_of_day()));

        ptime start{*date, startTime.time_of_day()};

        time_duration duration{minutes(60)};
        auto &ts = problem.addTimeslot(title, start, duration);

        for (auto it = tags.begin(); it != tags.end(); it++)
            ts.addTag(*it);

        ts.setTagPriority("Focus", 3);
    }

}

void getSecond(Problem<std::string, std::string, std::string, std::string> &problem) {

    using namespace boost::gregorian;
    using namespace boost::posix_time;

    problem.addGroup("Uni");
    problem.addGroup("Lecture");
    problem.addGroup("Tutorial");
    problem.addGroup("Exercise");

    problem.addTag("Focus");

    // --- DSAL ---
    problem.addGroup("DSAL");

    // Lecture: 12.04.2021 - 19.07.2021, 08:30-10:00, Lecture: 08:30 - 10:00, 15.04.2021 to 22.07.2021
    addLecture(problem, time_from_string("2021-04-12 08:30:00.000"), from_string("2021-07-19"), {"DSAL", "Lecture"});
    addLecture(problem, time_from_string("2021-04-15 08:30:00.000"), from_string("2021-07-22"), {"DSAL", "Lecture"});

    //        \item Exercises (global):
    //         Thursday 14:30 - 16:00, 15.04.2021 to 22.07.2021
    addLecture(problem, time_from_string("2021-04-15 14:30:00.000"), from_string("2021-07-22"), {"DSAL", "Exercise"});

    //        \item Tutorials:
    //         Thursday 10:30 - 12:00, 15.04.2021 to 22.07.2021
    //         OR  Friday 08:30 - 10:00, 16.04.2021 to 23.07.2021
    addLecture(problem, time_from_string("2021-04-15 10:30:00.000"), from_string("2021-07-22"), {"DSAL", "Tutorial", "DSAL1"});
    addLecture(problem, time_from_string("2021-04-16 08:30:00.000"), from_string("2021-07-23"), {"DSAL", "Tutorial", "DSAL2"});
    problem.oneOf({"DSAL1", "DSAL2"});


    // --- BuS ---
    problem.addGroup("BuS");
    problem.addGroup("BuSTut1");
    problem.addGroup("BuSTut2");
    problem.addGroup("BuSTut3");

    // Vorlesungen:
    // Dienstag , 10:30 - 12:00 von 13.04.2021 bis 20.07.2021
    addLecture(problem, time_from_string("2021-04-13 10:30:00.000"), from_string("2021-07-20"), {"BuS", "Lecture"});

    // Montag , 16:30 - 18:00 von 19.04.2021 bis 19.07.2021
    addLecture(problem, time_from_string("2021-04-19 16:30:00.000"), from_string("2021-07-19"), {"BuS", "Lecture"});

    // Exercise:
    // Freitag , 16:30 - 18:00 von 16.04.2021 bis 23.07.2021
    addLecture(problem, time_from_string("2021-04-16 16:30:00.000"), from_string("2021-07-23"), {"BuS", "Exercise"});

    // Add one of:
    //  Freitag , 10:30 - 12:00 von 16.04.2021 bis 23.07.2021
    //  Freitag , 14:30 - 16:00 von 16.04.2021 bis 23.07.2021
    //  Freitag , 14:30 - 16:00 von 16.04.2021 bis 23.07.2021
    addLecture(problem, time_from_string("2021-04-16 10:30:00.000"), from_string("2021-07-23"), {"BuS", "Tutorial"});
    addLecture(problem, time_from_string("2021-04-16 14:30:00.000"), from_string("2021-07-23"), {"BuS", "Tutorial"});
    addLecture(problem, time_from_string("2021-04-16 14:30:00.000"), from_string("2021-07-23"), {"BuS", "Tutorial"});
    problem.oneOf({"BuS1", "BuS2", "BuS3"});

    //addHomework();
    addReview(problem, time_from_string("2021-04-19 08:30:00.000"), from_string("2021-07-26"), {"BuS", "Review"});

    // -------------
    // FoSAP:
    // Vorlesungen: Dienstag , 16:30 - 18:00 von 13.04.2021 bis 20.07.2021, Donnerstag , 16:30 - 18:00 von 15.04.2021 bis 22.07.2021
    addLecture(problem, time_from_string("2021-04-13 16:30:00.000"), from_string("2021-07-20"), {"FoSAP", "Lecture"});
    addLecture(problem, time_from_string("2021-04-15 16:30:00.000"), from_string("2021-07-22"), {"FoSAP", "Lecture"});

    //%- Globalübung:
    //% Montag , 14:30 - 16:00 von 12.04.2021 bis 19.07.2021
    addLecture(problem, time_from_string("2021-04-12 14:30:00.000"), from_string("2021-07-19"), {"FoSAP", "Exercise"});

    //%- Tutorien:
    //% Donnerstag , 12:30 - 14:00 von 15.04.2021 bis 22.07.2021
    //% Donnerstag , 18:30 - 20:00 von 15.04.2021 bis 22.07.2021
    //% Montag , 16:30 - 18:00 von 12.04.2021 bis 19.07.2021
    //% Montag , 08:30 - 10:00 von 12.04.2021 bis 19.07.2021
    addLecture(problem, time_from_string("2021-04-15 12:30:00.000"), from_string("2021-07-22"), {"FoSAP", "Tutorial", "FoSAP1"});
    addLecture(problem, time_from_string("2021-04-15 18:30:00.000"), from_string("2021-07-22"), {"FoSAP", "Tutorial", "FoSAP2"});
    addLecture(problem, time_from_string("2021-04-12 16:30:00.000"), from_string("2021-07-19"), {"FoSAP", "Tutorial", "FoSAP3"});
    addLecture(problem, time_from_string("2021-04-12 08:30:00.000"), from_string("2021-07-19"), {"FoSAP", "Tutorial", "FoSAP4"});
    problem.oneOf({"FoSAP1", "FoSAP2", "FoSAP3", "FoSAP4"});



    // ---------------
    // LA:
    problem.addGroup("LA");

    // Vorlesungen:
    // Dienstag , 08:30 - 10:00 von 13.04.2021 bis 20.07.2021
    // Freitag , 08:30 - 10:00 von 16.04.2021 bis 23.07.2021
    addLecture(problem, time_from_string("2021-04-13 08:30:00.000"), from_string("2021-07-20"), {"LA", "Lecture"});
    addLecture(problem, time_from_string("2021-04-16 08:30:00.000"), from_string("2021-07-23"), {"LA", "Lecture"});

    // Globalübung:
    // Mittwoch , 08:30 - 10:00 von 14.04.2021 bis 21.07.2021
    addLecture(problem, time_from_string("2021-04-14 08:30:00.000"), from_string("2021-07-21"), {"LA", "Exercise"});

    // Tutorien: 19.-23.4.2021, to 12.-16.7.2021
    // Mittwoch 10:30-12:00 Uhr / 12:30-14:00 Uhr / 14:30-16:00 Uhr / 16:30-18:00 Uhr
    // Donnerstag 10:30-12:00 Uhr / 12:30-14:00 Uhr
    addLecture(problem, time_from_string("2021-04-21 10:30:00.000"), from_string("2021-07-21"), {"LA", "Tutorial", "LA1"});
    addLecture(problem, time_from_string("2021-04-21 12:30:00.000"), from_string("2021-07-21"), {"LA", "Tutorial", "LA2"});
    addLecture(problem, time_from_string("2021-04-21 14:30:00.000"), from_string("2021-07-21"), {"LA", "Tutorial", "LA3"});
    addLecture(problem, time_from_string("2021-04-21 16:30:00.000"), from_string("2021-07-21"), {"LA", "Tutorial", "LA4"});
    addLecture(problem, time_from_string("2021-04-22 10:30:00.000"), from_string("2021-07-22"), {"LA", "Tutorial", "LA5"});
    addLecture(problem, time_from_string("2021-04-22 12:30:00.000"), from_string("2021-07-22"), {"LA", "Tutorial", "LA6"});
    problem.oneOf({"LA1", "LA2", "LA3", "LA4", "LA5", "LA6"});

    // Homework, Review
    //addHomework(problem, );
    //addReview(problem, );

    // ---------------------
    // Proseminar



    // ---------------------
    // Exercise and Chores


    // ---------------------
    // Create Timeslots

    //addTimeslots(startDate, endDate, startTime, duration, std::initiliazerList<TagID>);

}