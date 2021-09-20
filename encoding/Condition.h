//
// Created by hal on 07.09.21.
//

#ifndef OMTSCHED_CONDITION_H
#define OMTSCHED_CONDITION_H

class Condition {

public:
    parameters;
    virtual Formula generate();
    virtual bool evaluate();

};


class OneOf : public Condition {};

OneOf::OneOf(){

}

Formula OneOf::generate() {

}



#endif //OMTSCHED_CONDITION_H
