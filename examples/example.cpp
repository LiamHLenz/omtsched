//
// Created by hal on 12.12.21.
//

#include "../omtsched.h"
#include "zebra.cpp"

int main() {

    omtsched::Problem<std::string> problem;
    getZebra(problem);
    omtsched::TranslatorZ3<std::string> translatorZ3(problem);
    //translatorZ3.solve();
    //omtsched::Model<std::string> model = translatorZ3.getModel();
    //model.print(std::cout);

}