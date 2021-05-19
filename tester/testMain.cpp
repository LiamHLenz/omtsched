//
// Created by dana on 27.04.21.
//

#include "../omtsched.h"

void getSecond(Problem<std::string, std::string, std::string, std::string> &problem);

int main() {

    hello();

    Problem<std::string, std::string, std::string, std::string> second_semester {"RWTH2ndSemesterCS", Unit::MINUTES, boost::posix_time::time_from_string("2021-04-12 08:00:00.000")};
    getSecond(second_semester);

    Translator<std::string, std::string, std::string, std::string> translator;
    //translator.saveEncoding(second_semester);
    translator.solve(second_semester, Translator<std::string, std::string, std::string, std::string>::Solver::Z3);

    return 0;
}
