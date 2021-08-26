//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_ASSIGNMENT_H
#define OMTSCHED_ASSIGNMENT_H

class Assignment {

public:
    virtual Formula generate() const;

private:
    std::vector<std::shared_ptr<Component>> components;

};


#endif //OMTSCHED_ASSIGNMENT_H
