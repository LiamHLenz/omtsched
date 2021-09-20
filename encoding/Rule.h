//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_RULE_H
#define OMTSCHED_RULE_H

enum class Operator {

    NOT, AND, OR, IMPLIES, IFF, EQUAL, UNEQUAL, INGROUP, INSET
};

class Expression {

public:
    //virtual Formula generate() const;

};

class Rule : public Expression {

public:
    //Formula generate() const override;
    //Condition conditions;
    bool validate() const;

private:


};

class Function : public Expression {

public:
    //Formula generate() const override;

};

#endif //OMTSCHED_RULE_H
