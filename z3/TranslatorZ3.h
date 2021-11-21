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
    struct SlotMap {

    public:
        z3::expr getVariable(const ID &, const ID &) const;

        std::pair<ID, ID> getSlot(const z3::expr &) const;

        /**
         *
         * @return [{id, id}, expr]
         */
        auto &getSlotMap();

        /**
         *
         * @return [expr, {id, id}]
         */
        auto &getVariableMap();

        void set(const ID &, const ID &, const z3::expr &);

        void remove(const ID &, const ID &);

        void remove(const z3::expr &);

    private:

        using bm_type = typename boost::bimap< std::pair<ID, ID>, z3::expr>::value_type;

        // z3::sort does not define an order, so we use 2 unordered maps instead of a bimap
        //std::map<std::pair<ID, ID>, z3::expr> variables;
        //std::map<z3::expr, std::pair<ID, ID>> slots;
        boost::bimap<std::pair<ID, ID>, z3::expr> slots;

    };

    template<typename ID>
    z3::expr SlotMap<ID>::getVariable(const ID &assignment, const ID &slot) const {
        return slots.left.at({assignment, slot});
    }

    template<typename ID>
    std::pair<ID, ID> SlotMap<ID>::getSlot(const z3::expr &expr) const {
        return slots.right.at(expr);
    }


    template<typename ID>
    void SlotMap<ID>::set(const ID &assignment, const ID &slot, const z3::expr &expr) {
        //TODO: any type of error checking anywhere

        /* typedef bimap< int, list_of< std::string > > bm_type;
            bm_type bm;
            bm.insert( bm_type::relation( 1, "one" ) );*/

        slots.insert(bm_type(std::make_pair(assignment, slot), expr));
        //slots.left.insert(std::make_pair(assignment, slot), expr);
    }

    template<typename ID>
    void SlotMap<ID>::remove(const ID &assignment, const ID &slot) {
        //const auto &sort = componentTypeSorts.at({assignment, slot});
        //slots.erase(sort);
        //variables.erase({assignment, slot});
        slots.left.erase({assignment, slot});
    }

    template<typename ID>
    void SlotMap<ID>::remove(const z3::expr &expr) {
        //const auto &id = componentTypeNames.at(sort);
        //componentTypeNames.erase(sort);
        //componentTypeSorts.erase(id);
        slots.right.erase(expr);
    }

    template<typename ID>
    auto &SlotMap<ID>::getSlotMap() {
        return slots.left;
    }

    template<typename ID>
    auto &SlotMap<ID>::getVariableMap() {
        return slots.right;
    }



    template<typename ID>
    class TranslatorZ3 : public omtsched::Translator<ID> {
    public:
        TranslatorZ3(const Problem <ID> &problem);

        void solve() override;

        Model<ID> getModel() override;

        z3::context &getContext();

        //const z3::expr getComponent(const ID &component);

        const ID getComponent(const z3::expr &) const;

        bool isSAT() override;

    private:

        void setupVariables();
        void setupConstants();
        void setupUniqueness();

        void resolveRule(const Rule <ID> &rule);

        void addToSolver(const z3::expr &condition, const bool &hard, const int &weight);

        //const z3::expr getVariable(const Assignment <ID> &assignment, const std::string &componentSlot) const;
        const z3::expr getVariable(const ID &assignment, const ID &componentSlot) const;
        const z3::expr getConstant(const ID &component) const;


        z3::expr resolveCondition(const Condition <ID> &condition, const std::vector<Assignment<ID>*> &asgnComb);
        z3::expr resolveComponentIs(const ComponentIs <ID> &, const Assignment<ID>* asgn);
        //z3::expr resolveComponentIn(const ComponentIn <ID> &, const Assignment<ID>* asgn);
        z3::expr resolveSameComponent(const SameComponent <ID> &, const std::vector<Assignment<ID>*> asgnComb);
        z3::expr resolveInGroup(const InGroup <ID> &, const Assignment<ID> asgn);
        //z3::expr resolveMaxAssignments(const MaxAssignment <ID> &, const std::vector<Assignment<ID>*> asgnComb);

        z3::context context;
        std::unique_ptr<z3::solver> solver;

        std::map<ID, z3::sort> sortMap;
        boost::bimap<ID, z3::expr> components;
        // tuple in order: assignment, slot name
        //boost::bimap<std::pair<int, std::string>, z3::expr> slots;
        SlotMap<ID> slots;

    };

    template<typename ID>
    TranslatorZ3<ID>::TranslatorZ3(const Problem <ID> &problem) : Translator<ID>{problem} {

        setupConstants();
        setupVariables();
        solver = std::make_unique<z3::solver>(context);
        setupUniqueness();
    }


    template<typename ID>
    z3::context &TranslatorZ3<ID>::getContext() {
        return context;
    }

    /*
    template<typename ID>
    const z3::expr TranslatorZ3<ID>::getVariable(const Assignment <ID> &assignment, const std::string &componentSlot) const {

        auto assignmentNumber = getAssignmentNumber(assignment);
        return slots.getSort(assignmentNumber, componentSlot);
    }*/

    template<typename ID>
    const z3::expr TranslatorZ3<ID>::getVariable(const ID &assignment, const ID &componentSlot) const {
        slots.getSlot(assignment, componentSlot);
    }

    template<typename ID>
    const z3::expr TranslatorZ3<ID>::getConstant(const ID &component) const {
        return components.left.at(component);
    }

    //   template<typename ID>
    //   const z3::expr TranslatorZ3<ID>::getComponent(const ID &component) {
    //      return components.at(component);
    //   }

    template<typename ID>
    void TranslatorZ3<ID>::setupUniqueness(){

        for(const auto &type : this->problem.getComponentTypes()){

            z3::expr_vector vars {context};
            for(const Component<ID> &var : this->problem.getComponents(type))
                vars.push_back(components.left.at(var.getID()));

            solver->add( z3::distinct(vars));
        }

    }

    template<typename ID>
    void TranslatorZ3<ID>::setupVariables() {
        int a = 0;
        for (const auto &[aid, assignment] : this->problem.getAssignments()) {
            int c = 0;
            for (const auto &[sname, slot] : assignment.getComponentSlots()) {
                // create assignment variable
                const auto &type = sortMap.at(slot.type);
                std::string name = "a" + std::to_string(a) + "c" + sname;
                slots.set(aid, sname, context.constant(name.c_str(), type));
                c++;
            }
            a++;
        }

    }

    template<typename ID>
    void TranslatorZ3<ID>::setupConstants() {

        // components are stored in a map by type:
        // std::map<ID, std::vector<Component<ID>>> components;

        for(const ID &type : this->problem.getComponentTypes()) {

            z3::sort typeExpr = context.uninterpreted_sort(static_cast<std::string>(type).c_str());
            sortMap.emplace(type, typeExpr);

            int count = 0;
            for(const auto &component : this->problem.getComponents(type)) {

                z3::expr var = context.constant(("c"+std::to_string(count)).c_str(), sortMap.at(type));
                components.left.insert(std::make_pair(component.getID(), var));
                count++;
            }

        }

    }

    template<typename ID>
    void TranslatorZ3<ID>::solve() {

        const auto result = solver->check();

        if (result == z3::unsat)
            std::cout << "UNSAT" << std::endl;

        else if (result == z3::sat) {

            std::cout << "SAT" << std::endl;
            z3::model m = solver->get_model();
        } else if (result == z3::unknown)
            std::cout << "UNKNOWN" << std::endl;


    }

    template<typename ID>
    Model<ID> TranslatorZ3<ID>::getModel() {

        Model<ID> model;

        if(!solver->check() == z3::sat)
            return model;

        z3::model m = solver->get_model();

        for(const auto &[aid, asgn] : this->problem.getAssignments())
            for(const auto &[sid, slot] : asgn.getComponentSlots()){

                const z3::expr &var = getVariable(aid, sid);
                const z3::expr &result = m.eval(var);
                const ID component = getComponent(result);

                model.setComponent(aid, sid, component);
            }

        return model;

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
               return resolveComponentIs(condition, asgnComb);

           case CONDITION_TYPE::COMPONENT_IN:
               return resolveComponentIn(condition, asgnComb);

           case CONDITION_TYPE::SAME_COMPONENT:
               return resolveSameComponent(condition, asgnComb);

           case CONDITION_TYPE::IN_GROUP:
               return resolveInGroup(condition, asgnComb);

           case CONDITION_TYPE::MAX_ASSIGNMENTS:
               return resolveMaxAssignments(condition, asgnComb);

       }

   }

   template<typename ID>
   bool isViable(const Condition<ID> &condition, const std::vector<Assignment<ID> *> &asgnSet) {

       // TODO: implement isViable
       return true;

   }

   template<typename ID>
   void TranslatorZ3<ID>::resolveRule(const Rule <ID> &rule) {

       const Condition<ID> &c = rule.getTopCondition();

       if(rule.isRestricted())
           for(const std::vector<Assignment<ID> *> &asgnSet : rule.getApplicableSets())
               addToSolver(resolveCondition(c, asgnSet));

       else
           for(const std::vector<Assignment<ID> *> &asgnSet : this->problem.getAssignmentCombinations())
               if(isViable(c, asgnSet)) // TODO: check symmetry
                   addToSolver(resolveCondition(c, asgnSet));

   }


template<typename ID>
bool TranslatorZ3<ID>::isSAT() {

    return solver->check() == z3::sat;
}


template<typename ID>
const ID TranslatorZ3<ID>::getComponent(const z3::expr &variable) const {
    return components.at(variable);
}


}


#endif //OMTSCHED_TRANSLATORZ3_H
