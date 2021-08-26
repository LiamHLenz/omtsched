//
// Created by admin on 24.08.2021.
//

omtsched::Problem inrc("INRC2");

using Nurse = omtsched::Agent;
using Shift = omtsched::TimedTask;

class ShiftAssignment : public Assignment {

    Nurse nurse;
    Shift shift;

    Formula generate() const override;

};

bool operator<(const ShiftAssignment &lhs, const ShiftAssignment &rhs){
    return lhs.shift < rhs.shift;
}

// create nurses
for() {

    Nurse name;

}

// create shifts