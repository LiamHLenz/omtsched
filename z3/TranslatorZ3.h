//
// Created by dana on 11.05.21.
//

#ifndef OMTSCHED_TRANSLATORZ3_H
#define OMTSCHED_TRANSLATORZ3_H


#include "../Translator.h"
#include "maps.h"
#include <z3.h>
#include <z3++.h>
#include <map>
#include <boost/bimap.hpp>


namespace omtsched {

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
        const z3::expr &getVariable(const ID &assignment, const ID &componentSlot) const;
        const z3::expr &getConstant(const ID &component) const;
        
        z3::expr getComponentExpr(const ID &id);


        z3::expr resolveCondition(const Condition <ID> &condition, const std::vector<Assignment<ID>*> &asgnComb);
        z3::expr resolveComponentIs(const ComponentIs <ID> &, const Assignment<ID>* asgn);
        //z3::expr resolveComponentIn(const ComponentIn <ID> &, const Assignment<ID>* asgn);
        z3::expr resolveSameComponent(const SameComponent <ID> &, const std::vector<Assignment<ID>*> asgnComb);
        z3::expr resolveInGroup(const InGroup <ID> &, const Assignment<ID> asgn);
        //z3::expr resolveMaxAssignments(const MaxAssignment <ID> &, const std::vector<Assignment<ID>*> asgnComb);

        z3::context context;
        std::unique_ptr<z3::solver> solver;

        SortMap<ID> sorts;
        ComponentMap<ID> components;
        SlotMap<ID> slots;
        
        std::vector<z3::func_decl_vector> enum_consts;
        std::vector<z3::func_decl_vector> enum_testers;

    };

    template<typename ID>
    TranslatorZ3<ID>::TranslatorZ3(const Problem <ID> &problem) : Translator<ID>{problem},
        components{problem}, slots{context}, sorts{context, components} {

        //define sorts
        int typeCount = 0;
        
        for(const ID &type : this->problem.getComponentTypes()) {

            std::string name = "s" + std::to_string(typeCount);
            
            enum_consts.emplace_back(context);
            enum_testers.emplace_back(context);
            
            //set(const ID &type, const std::string &name, std::vector<z3::func_decl_vector>&, std::vector<z3::func_decl_vector>&);

            sorts.set(type, name, this->problem.getComponents(type), enum_consts, enum_testers);
   
            typeCount++; 

        }
        
        //define slots
        setupVariables();
        
        solver = std::make_unique<z3::solver>(context);
        //setupUniqueness();
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
    const z3::expr &TranslatorZ3<ID>::getVariable(const ID &assignment, const ID &componentSlot) const {
        return slots.getVariable(assignment, componentSlot);
    }

    template<typename ID>
    const z3::expr &TranslatorZ3<ID>::getConstant(const ID &component) const {
        return components.getVariable(component);
    }
    
    template<typename ID>
    z3::expr TranslatorZ3<ID>::getComponentExpr(const ID &id) {
        
        
    }

    template<typename ID>
    void TranslatorZ3<ID>::setupUniqueness(){

        for(const auto &type : this->problem.getComponentTypes()){

            z3::expr_vector vars {context};
            for(const Component<ID> &component : this->problem.getComponents(type))
                vars.push_back(getComponentExpr(component.getID()));

            if(!vars.empty())
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
                const z3::sort &type = sorts.getSort(slot.type);
                const std::string &name = "a" + std::to_string(a) + "c" + sname;
                slots.set(aid, sname, type, name);
                c++;
            }
            a++;
        }

    }

    template<typename ID>
    void TranslatorZ3<ID>::setupConstants() {

    
        /*
        int typeCount = 0;
        for(const ID &type : this->problem.getComponentTypes()) {

            std::string name = "t" + std::to_string(typeCount);
            //sorts.set(type, name);
            typeCount++;

            sorts.set(type, name, this->problem.getComponents(type));
            
            
            for(const auto &component : this->problem.getComponents(type)) {

                std::string name = "c"+std::to_string(count);
                const z3::sort &srt = sorts.getSort(type);
                components.set(component.getID(), name, srt);
                
                count++;
            }

        }*/

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
        
        std::cout << m << std::endl;
    
        std::cout << "Test model: " << std::endl;
        for(const auto &[aid, asgn] : this->problem.getAssignments())
            for(const auto &[sid, slot] : asgn.getComponentSlots()){

                const z3::expr &var = getVariable(aid, sid);
                const z3::expr &result = m.eval(var);
                
                std::cout << "Slot: (" << aid << ", " << sid << "): " << result << std::endl;
                
                
                //const ID component = getComponent(result);

                //model.setComponent(aid, sid, component);
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
    return components.getComponent(variable);
}


}


#endif //OMTSCHED_TRANSLATORZ3_H
