//
// Created by dana on 11.05.21.
//

#ifndef OMTSCHED_TRANSLATORZ3_H
#define OMTSCHED_TRANSLATORZ3_H


#include "../Translator.h"
#include <z3.h>
#include <z3++.h>
#include <map>
#include <boost/bimap.hpp>


template<>
struct std::hash<z3::sort> {
    std::size_t operator()(const z3::sort &sort) const noexcept {
        return sort.hash();
    }
};


namespace omtsched {

    /*
    * z3::sort does not define an order so boost::bimap cannot be used directly
    * This is a simple wrapper to circumvent that issue.
    */
    template<typename ID>
    struct sortMap {

    public:
        z3::sort getSort(const ID &) const;

        ID getType(const z3::sort &) const;

        void set(const ID &, const z3::sort &);

        void remove(const ID &);

        void remove(const z3::sort &);

    private:

        // z3::sort does not define an order, so we use 2 unordered maps instead of a bimap
        std::unordered_map<ID, z3::sort> componentTypeSorts;
        std::unordered_map<z3::sort, ID> componentTypeNames;

    };

    template<typename ID>
    z3::sort sortMap<ID>::getSort(const ID &id) const {
        return componentTypeSorts.at(id);
    }

    template<typename ID>
    ID sortMap<ID>::getType(const z3::sort &sort) const {
        return componentTypeNames.at(sort);
    }

    template<typename ID>
    void sortMap<ID>::set(const ID &id, const z3::sort &sort) {
        //TODO: any type of error checking anywhere
        componentTypeNames[id] = sort;
        componentTypeSorts[sort] = id;
    }

    template<typename ID>
    void sortMap<ID>::remove(const ID &id) {
        const auto &sort = componentTypeSorts.at(id);
        componentTypeNames.erase(sort);
        componentTypeSorts.erase(id);
    }

    template<typename ID>
    void sortMap<ID>::remove(const z3::sort &sort) {
        const auto &id = componentTypeNames.at(sort);
        componentTypeNames.erase(sort);
        componentTypeSorts.erase(id);
    }

    template<typename ID>
    class TranslatorZ3 : public omtsched::Translator<ID> {
    public:
        TranslatorZ3(const Problem <ID> &problem);

        void solve() override;

        Model getModel() override;

        z3::context &getContext();

        const z3::expr getVariable(const Assignment <ID> &assignment, const std::string &componentSlot, int num);

        const z3::expr getComponent(const ID &component);

    private:
        void setupVariables();

        z3::expr resolveRule(const Rule <ID> &rule);

        void addToSolver(const z3::expr &condition, const bool &hard, const int &weight);

        int getAssignmentNumber(const Assignment <ID> &assignment);

        z3::expr resolveCondition(const Condition <ID> &condition, const std::vector<Assignment<ID>*> asgnComb);
        z3::expr resolveComponentIs(const ComponentIs <ID> &, const std::vector<Assignment<ID>*> asgnComb);
        z3::expr resolveComponentIn(const ComponentIn <ID> &, const std::vector<Assignment<ID>*> asgnComb);
        z3::expr resolveSameComponent(const SameComponent <ID> &, const std::vector<Assignment<ID>*> asgnComb);
        z3::expr resolveInGroup(const InGroup <ID> &, const std::vector<Assignment<ID>*> asgnComb);
        z3::expr resolveMaxAssignments(const MaxAssignment <ID> &, const std::vector<Assignment<ID>*> asgnComb);

        z3::context context;
        z3::solver solver;
        Problem<ID> &problem;

        //TODO: double map
        boost::bimap<int, Assignment < ID>*> assignmentOrder;

        sortMap<ID> sortMap;
        boost::bimap<ID, z3::expr> components;
        // tuple in order: assignment, slot name, i-th part
        boost::bimap<std::tuple<int, std::string, int>, z3::expr> slots;

        z3::expr resolveComponentIs(const ComponentIs <ID> &c, const Assignment <ID> *&asgn);
    };

    template<typename ID>
    TranslatorZ3<ID>::TranslatorZ3(const Problem <ID> &problem) : problem{problem} {

        setup(problem);
    }

    template<typename ID>
    int TranslatorZ3<ID>::getAssignmentNumber(const Assignment <ID> &assignment) {

        return assignmentOrder.at(assignment);
    }

    template<typename ID>
    z3::context &TranslatorZ3<ID>::getContext() {
        return context;
    }

    template<typename ID>
    const z3::expr
    TranslatorZ3<ID>::getVariable(const Assignment <ID> &assignment, const std::string &componentSlot, int num) {

        auto assignmentNumber = getAssignmentNumber(assignment);
        return slots.left.at({assignmentNumber, componentSlot, num});
    }

    template<typename ID>
    const z3::expr TranslatorZ3<ID>::getComponent(const ID &component) {
        return components.at(component);
    }

    template<typename ID>
    void TranslatorZ3<ID>::setupVariables() {
        //TODO: make this not like this

        // Create component types and components
        for (const auto &compType: this->problem.getComponentTypes()) {
            const ID &typeID = compType.getID();
            sortMap.set(typeID, context.uninterpreted_sort(compType));
            // Components
            size_t ccount = 0;
            z3::expr_vector comps{context};
            for (const auto &component: this->problem.getComponents(compType)) {

                // Assign an internal numerical ID
                const z3::sort &type = sortMap.get(typeID);
                const std::string name = "c" + std::to_string(ccount);
                components[component] = context.constant(name.c_str(), type);
                ccount++;
                comps.push_back(components.at(component));
            }
            // Components are assumed to be unique
            addRule(z3::distinct(comps));
        }

        // Create Assignments
        int a = 0;
        for (const auto &assignment : this->problem.getAssignments()) {
            assignmentOrder[a] = &assignment;
            int c = 0;
            for (const auto &slot: assignment->getSlots()) {
                int i = 0;
                for (const auto &component : slot.components) {
                    // create assignment variable
                    const auto &type = sortMap.get(component.getType());
                    std::string name = "a" + std::to_string(a) + "c" + std::to_string(c) + "i" + std::to_string(i);
                    slots[{a, slot.getName(), i}] = context.constant(name.c_str(), type);
                    i++;
                }
                c++;
            }
            a++;
        }

        solver = z3::solver{context};

    }


    template<typename ID>
    void TranslatorZ3<ID>::solve() {

        const auto result = solver.check();

        if (result == z3::unsat)
            std::cout << "UNSAT" << std::endl;

        else if (result == z3::sat) {

            std::cout << "SAT" << std::endl;
            z3::model m = solver.get_model();
        } else if (result == z3::unknown)
            std::cout << "UNKNOWN" << std::endl;


    }


    template<typename ID>
    z3::expr TranslatorZ3<ID>::resolveComponentIs(const ComponentIs <ID> &c, const Assignment<ID>* &asgn){

        /*
         * //If there is more than one assignment: conjunction
        z3::expr_vector equalities (t.getContext());
        for(const auto &assignment : assignmentGroups) {
            const z3::expr &var = t.getVariable(assignment, componentSlot);
            const z3::expr &component = t.getComponent(component);
            equalities.push_back(var == component);
        }

        return z3::mk_and(equalities);
         *
         */
        // Slot of assignment ? is component ?
        std::string compSlotID = components.componentSlot;
        ComponentSlot<ID> slot = asgn->getComponentSlots(compSlotID);

        z3::expr comp = components.at(c.component);
        boost::bimap<std::tuple<int, std::string, int>, z3::expr> slots;

        // TODO: ???
    }


    template<typename ID>
    z3::expr TranslatorZ3<ID>::resolveComponentIn(const ComponentIn <ID> &c, const std::vector<Assignment<ID>*> &asgnComb){}


    template<typename ID>
    z3::expr TranslatorZ3<ID>::resolveSameComponent(const SameComponent <ID> &c, const std::vector<Assignment<ID>*> &asgnComb){}


    template<typename ID>
    z3::expr TranslatorZ3<ID>::resolveInGroup(const InGroup <ID> &c, const std::vector<Assignment<ID>*> &asgnComb){}


    template<typename ID>
    z3::expr TranslatorZ3<ID>::resolveMaxAssignment(const MaxAssignment <ID> &c, const std::vector<Assignment<ID>*> &asgnComb){

        /*
    * Resolved by:
    * 1. creating a bitvector of (relevant) assignments
    * 2. creating an implication for each assignment: if the conditions are met the
    *    bit corresponding to the assignment is set
    * 3. constraining the maximum number of set bits
    */
   }


   template<typename ID>
   z3::expr TranslatorZ3<ID>::resolveCondition(const Condition <ID> &condition, const std::vector<Assignment<ID>*> &asgnComb) {

       z3::expr_vector z3args{context};
       CONDITION_TYPE type = condition->getType();
       switch (type) {

           case CONDITION_TYPE::NOT:
               return !condition->subcondition;

           case CONDITION_TYPE::OR:
               for (const auto s : condition->subconditions)
                   z3args.push_back(resolveCondition(s, asgnComb));
               return z3::mk_or(z3args);

           case CONDITION_TYPE::AND:
               for (const auto s : condition->subconditions)
                   z3args.push_back(resolveCondition(s, asgnComb));
               return z3::mk_and(z3args);

           case CONDITION_TYPE::XOR:
               return (resolveCondition(condition.first, asgnComb) && !resolveCondition(condition.second, asgnComb))
               || (!resolveCondition(condition.first, asgnComb) && resolveCondition(condition.second, asgnComb));

           case CONDITION_TYPE::IMPLIES:
               return z3::implies(resolveCondition(condition->antecedent, asgnComb), resolveCondition(condition->consequent, asgnComb));

           case CONDITION_TYPE::IFF:
               return z3::implies(resolveCondition(condition->antecedent, asgnComb), resolveCondition(condition->consequent, asgnComb))
               && z3::implies(resolveCondition(condition->consequent, asgnComb), resolveCondition(condition->antecedent, asgnComb));

           case CONDITION_TYPE::COMPONENT_IS:
               return resolveComponentIs(const Condition <ID> &);

           case CONDITION_TYPE::COMPONENT_IN:
               return resolveComponentIn(const Condition <ID> &);

           case CONDITION_TYPE::SAME_COMPONENT:
               return resolveSameComponent(const Condition <ID> &);

           case CONDITION_TYPE::IN_GROUP:
               return resolveInGroup(const Condition <ID> &);

           case CONDITION_TYPE::MAX_ASSIGNMENTS:
               return resolveMaxAssignments(const Condition <ID> &);

       }

   }

   template<typename ID>
   bool isViable(const Condition<ID> &condition, const std::vector<Assignment<ID> *> &asgnSet) {

       // TODO: implement isViable
       return true;

   }

   template<typename ID>
   z3::expr TranslatorZ3<ID>::resolveRule(const Rule <ID> &rule) {

       const Condition<ID> &c = rule.getTopCondition();

       if(rule.isRestricted())
           for(const std::vector<Assignment<ID> *> &asgnSet : rule.getApplicableSets())
               addToSolver(resolveCondition(c, asgnSet));

       else
           for(const std::vector<Assignment<ID> *> &asgnSet : problem.getAssignmentCombinations())
               if(isViable(c, asgnSet)) // TODO: check symmetry
                   addToSolver(resolveCondition(c, asgnSet));

   }


}

#endif //OMTSCHED_TRANSLATORZ3_H
