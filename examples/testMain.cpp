//
// Created by dana on 27.04.21.
//

#include "../omtsched.h"
#include "problems.h"

void getSecond(Problem<std::string, std::string, std::string, std::string> &problem);

int main() {

    Problem<std::string, std::string, std::string, std::string> second_semester {"RWTH2ndSemesterCS", Unit::MINUTES, boost::posix_time::time_from_string("2021-04-12 08:00:00.000")};
    getSecond(second_semester);

    TranslatorZ3<std::string, std::string, std::string, std::string> translator;
    //translator.saveEncoding(second_semester);
    translator.solve(second_semester, TranslatorZ3<std::string, std::string, std::string, std::string>::Solver::Z3);

    return 0;
}
