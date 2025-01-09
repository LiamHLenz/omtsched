#include "src/omtsched.h"
#include "examples/zebra.cpp"

int main() {


    // load problem (goal: load from textfile, parse .smt2) 
    // output solution in console (goal: write to file, .smt2 and readable)


    omtsched::Problem<std::string> example;
    getZebra(example);

    omtsched::Translator<std::string> trans {example};


    trans.print();

    trans.solve();


    if(trans.isSAT) {

        std::cout << "SAT" << std::endl;

    } else {

        std::cout << "UNSAT" << std::endl;

    }

}