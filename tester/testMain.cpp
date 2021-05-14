//
// Created by dana on 27.04.21.
//

#include "../omtsched.h"

void getSecond(Problem<std::string, std::string, std::string, std::string> &problem);

int main() {

    hello();

    Problem<std::string, std::string, std::string, std::string> second_semester {"RWTH2ndSemesterCS", Unit::MINUTES, boost::posix_time::time_from_string("2021-04-12 08:00:00.000")};
    getSecond(second_semester);
    //omtsched::solve(second_semester, omtsched::Solver::Z3);

    Translator<std::string, std::string, std::string, std::string> translator;
    translator.saveEncoding(second_semester);

    return 0;
}

void addLecture(Problem<std::string, std::string, std::string, std::string> &problem, boost::posix_time::ptime startTime, boost::gregorian::date endDate, std::string subject) {

    using namespace boost::gregorian;
    using namespace boost::posix_time;

    for(week_iterator date = startTime.date(); date < startTime.date() + weeks(1); ++date) {
//    for(week_iterator date = startTime.date(); date <= endDate; ++date) {

        std::string title = "Lecture_" + subject + "_" + boost::gregorian::to_iso_string(*date);
        ptime start {*date, startTime.time_of_day()};

        time_duration duration {minutes(120)};
        auto &task = problem.addTask(title, start, duration, start + duration, false);
        auto &ts = problem.addTimeslot(to_iso_string(start), start, duration);

        task.addGroup("Uni");
        task.addGroup(subject);

        ts.addGroup("Uni");
        ts.addGroup(subject);

        //TODO: bind
        problem.bind(task, ts, title + "-bound-" + ts.getID());

    }

}

// Definitions of some example problems

void getSecond(Problem<std::string, std::string, std::string, std::string> &problem) {

    using namespace boost::gregorian;
    using namespace boost::posix_time;

    problem.addGroup("Uni");

    // --- DSAL ---
    problem.addGroup("DSAL");

    // Lecture: 12.04.2021 - 19.07.2021, 08:30-10:00, Lecture: 08:30 - 10:00, 15.04.2021 to 22.07.2021
    addLecture(problem, time_from_string("2021-04-12 08:30:00.000"), from_string("2021-07-19"), "DSAL");
    addLecture(problem, time_from_string("2021-04-15 08:30:00.000"), from_string("2021-07-22"), "DSAL");

    //Exercise: 

    // -------------


}