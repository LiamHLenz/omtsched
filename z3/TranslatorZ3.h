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

        void print() const;

    private:

        void setupVariables();
        void setupConstants();
        void setupUniqueness();
        void setupExistence();

        //std::vector<std::vector<Assignment<ID> *>> generateAllAsgn(const Rule<ID> &rule);

        void resolveRule(const Rule <ID> &rule);

        void addToSolver(const z3::expr &condition, const bool &hard, const int &weight);

        //const z3::expr getVariable(const Assignment <ID> &assignment, const std::string &componentSlot) const;
        const z3::expr &getVariable(const ID &assignment, const ID &componentSlot) const;
        const z3::expr &getConstant(const ID &component) const;


        z3::expr resolveCondition(const std::shared_ptr<Condition <ID>> &condition, const Assignment<ID>* asgn = nullptr);
        z3::expr resolveComponentIs(const std::shared_ptr<Condition <ID>> &, const Assignment<ID> *asgn);
        //z3::expr resolveComponentIn(const std::shared_ptr<Condition <ID> &, const std::vector<Assignment<ID>*> &asgnComb);
        z3::expr resolveSameComponent(const std::shared_ptr<Condition <ID>> &,const std::vector<Assignment<ID>*> &asgnComb = {});
        z3::expr resolveInGroup(const std::shared_ptr<Condition <ID>> &, const std::vector<Assignment<ID>*> &asgnComb = {});
        //z3::expr resolveMaxAssignments(const std::shared_ptr<Condition <ID> &, const std::vector<Assignment<ID>*> &asgnComb);
        z3::expr resolveDistinct(const std::shared_ptr<Condition <ID>> &);

        const Problem<ID> &problem;

        z3::context context;
        std::unique_ptr<z3::solver> solver;

        SortMap<ID> sorts;
        //ComponentMap<ID> components;
        SlotMap<ID> slots;
        
        //std::vector<z3::func_decl_vector> enum_consts;
        //std::vector<z3::func_decl_vector> enum_testers;
        
        void addToSolver(const z3::expr &);

    };

    template<typename ID>
    TranslatorZ3<ID>::TranslatorZ3(const Problem <ID> &problem) : Translator<ID>{problem}, problem{problem},
    sorts{context, problem}, slots{context, problem, sorts} {

        
        solver = std::make_unique<z3::solver>(context);
        
        setupExistence();
        setupUniqueness();
        
        for(const Rule<ID> &rule : problem.getRules())
            resolveRule(rule);
        
    }


    template<typename ID>
    z3::context &TranslatorZ3<ID>::getContext() {
        return context;
    }
    
    template<typename ID>
    void TranslatorZ3<ID>::addToSolver(const z3::expr &constraint) {
    
            solver->add(constraint);
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
        return sorts.getConstant(component);
    }


    template<typename ID>
    void TranslatorZ3<ID>::setupExistence(){
        
        //Every assignment slot variable needs to have a value
        for(const auto &[aid, asgn] : problem.getAssignments()) {
            for(const auto &[sid, slot] : asgn.getComponentSlots()) {

                z3::expr_vector potentialValues {context};
                // TODO: optional slots
                // TODO: slots with limited set of potential values
                const z3::expr &slotVariable = getVariable(aid, sid);
                for(const auto &comp : problem.getComponents(slot.type)){
                    const z3::expr &component = getConstant(comp->getID());
                    z3::expr eqls {slotVariable == component};
                    potentialValues.push_back(eqls);
                }
                solver->add( z3::mk_or(potentialValues));
            }
                
        }
        
    }

    template<typename ID>
    void TranslatorZ3<ID>::setupUniqueness(){

        for(const auto &type : this->problem.getComponentTypes()){

            z3::expr_vector vars {context};
            for(const auto &component : this->problem.getComponents(type))
                vars.push_back(getConstant(component->getID()));

            if(!vars.empty()) {
                z3::expr dis = z3::distinct(vars);
                solver->add(dis);
            }
        }

    } 

    template<typename ID>
    void TranslatorZ3<ID>::setupVariables() {

        //slots.initialize(this->problem.getAssignments());

        /*
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
        }*/

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

        for(const auto &[aid, asgn] : this->problem.getAssignments())
            for(const auto &[sid, slot] : asgn.getComponentSlots()){

                const z3::expr &var = getVariable(aid, sid);
                const z3::expr &result = m.eval(var);

                const ID &component = getComponent(result);
                model.setComponent(aid, sid, component);
            }

        return model;

    }

   template<typename ID>
   z3::expr TranslatorZ3<ID>::resolveCondition(const std::shared_ptr<Condition <ID>> &condition, const Assignment<ID>* asgn) {

       z3::expr_vector z3args{context};
       CONDITION_TYPE type = condition->getType();
       switch (type) {
           
           case CONDITION_TYPE::BASE:
                assert(false && "Attempting to resolve a condition of a placeholder type.");

           case CONDITION_TYPE::NOT:
               return !resolveCondition(condition->subconditions.at(0));

           case CONDITION_TYPE::OR:
               for (const auto s : condition->subconditions)
                   z3args.push_back(resolveCondition(s));
               return z3::mk_or(z3args);

           case CONDITION_TYPE::AND:
               for (const auto s : condition->subconditions)
                   z3args.push_back(resolveCondition(s));
               return z3::mk_and(z3args);

           case CONDITION_TYPE::XOR:
               return (resolveCondition(condition->subconditions.at(0)) && !resolveCondition(condition->subconditions.at(1)))
               || (!resolveCondition(condition->subconditions.at(0)) && resolveCondition(condition->subconditions.at(1)));

           case CONDITION_TYPE::IMPLIES:{

               for(auto &[id, asgn] : problem.getAssignments()){
                   z3args.push_back(z3::implies(resolveCondition(condition->subconditions.at(0), &asgn),
                                                resolveCondition(condition->subconditions.at(1), &asgn)));
               }
               return z3::mk_and(z3args);
           }

           case CONDITION_TYPE::IFF:
               return z3::implies(resolveCondition(condition->subconditions.at(0)), resolveCondition(condition->subconditions.at(1)))
               && z3::implies(resolveCondition(condition->subconditions.at(1)), resolveCondition(condition->subconditions.at(0)));

           case CONDITION_TYPE::COMPONENT_IS:
               return resolveComponentIs(condition, asgn);

           //case CONDITION_TYPE::COMPONENT_IN:
           //    return resolveComponentIn(condition, asgnComb);

           case CONDITION_TYPE::SAME_COMPONENT:
               return resolveSameComponent(condition);

           case CONDITION_TYPE::IN_GROUP:
               return resolveInGroup(condition);

           case CONDITION_TYPE::DISTINCT:
               return resolveDistinct(condition);

           //case CONDITION_TYPE::MAX_ASSIGNMENTS:
           //    return resolveMaxAssignments(condition, asgnComb);

       }

   }

   template<typename ID>
   bool isViable(const Condition<ID> &condition, const std::vector<Assignment<ID> *> &asgnSet) {

       // TODO: implement isViable
       return true;

   }

   template<typename ID>
   void TranslatorZ3<ID>::resolveRule(const Rule <ID> &rule) {

       const auto &c = rule.getTopCondition();

       z3::expr e = resolveCondition(c);
       addToSolver(e);

        /*
       std::vector<std::vector<Assignment<ID> *>> appSets = rule.getApplicableSets();

       if(!rule.isRestricted())
           appSets = generateAllAsgn(rule);

        for(const std::vector<Assignment<ID> *> &asgnSet : rule.getApplicableSets())
            addToSolver(resolveCondition(c, asgnSet));
        */

   }


template<typename ID>
bool TranslatorZ3<ID>::isSAT() {

    return solver->check() == z3::sat;
}


template<typename ID>
const ID TranslatorZ3<ID>::getComponent(const z3::expr &variable) const {
    return sorts.getComponent(variable);
    //return components.getComponent(variable);
}


template<typename ID>
z3::expr TranslatorZ3<ID>::resolveComponentIs(const std::shared_ptr<Condition <ID>> &condition,
                                                        const Assignment<ID> *asgn) {

    auto c = std::dynamic_pointer_cast<ComponentIs<ID>>(condition);                                                        
    const z3::expr &component = getConstant(c->component);
    const z3::expr &var = getVariable(asgn->getID(), c->componentSlot);
    return var == component;

}

/*template<typename ID>
z3::expr TranslatorZ3::resolveComponentIn(const std::shared_ptr<ComponentIn <ID>> &c, const std::vector<Assignment<ID>*> &asgnComb) {

    z3::expr_vector equalities;
    for(const z3::expr &component : c.components) {

        const z3::expr &var = getVariable(*asgn, c.componentSlot);
        equalities.push_back( var == component );
    }

    return z3::mk_or(equalities);
}*/

template<typename ID>
z3::expr TranslatorZ3<ID>::resolveSameComponent(const std::shared_ptr<Condition <ID>>&condition, const std::vector<Assignment<ID>*> &asgnComb) {

    auto c = std::dynamic_pointer_cast<SameComponent<ID>>(condition);  
    
    z3::expr_vector equalities (context);
    for(auto it1 = asgnComb.begin(); it1 != asgnComb.end(); it1++)
        for(auto it2 = std::next(it1); it2 != asgnComb.end(); it2++) {

            const z3::expr &var1 = getVariable((*it1)->getID(), c->slot);
            const z3::expr &var2 = getVariable((*it2)->getID(), c->slot);
            equalities.push_back(var1 == var2);
        }
    return z3::mk_and(equalities);
}

template<typename ID>
z3::expr TranslatorZ3<ID>::resolveInGroup(const std::shared_ptr<Condition <ID>> &condition, const std::vector<Assignment<ID>*> &asgnComb) {

    auto c = std::dynamic_pointer_cast<InGroup<ID>>(condition);  
    /*
     * InGroup(const ID &componentType, ID groupID) : slot{slot}, group{groupID} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::IN_GROUP;
        const ID slot;
        const ID group;
     */

    const z3::expr &var = getVariable(asgnComb.at(0)->getID(), c->slot);
    // limits domain
    // get slot type
    const ID &type = asgnComb.at(0)->getSlot(c->slot).type;

    // std::map<ID, std::vector<Component<ID>>> components;
    z3::expr_vector equalities (context);
    for(const auto &component : this->problem.getComponents(type)){

        if(component->inGroup(c->group)) {
            const z3::expr &comp = getConstant(component->getID());
            equalities.push_back( var == comp );
        }

    }
    return z3::mk_or(equalities);

}

/*template<typename ID>
z3::expr TranslatorZ3::resolveMaxAssignments(const std::shared_ptr<MaxAssignment <ID>> &c, const std::vector<Assignment<ID>*> &asgnComb){

}*/



    template<typename ID>
    z3::expr TranslatorZ3<ID>::resolveDistinct(const std::shared_ptr<Condition <ID>> &condition) {

        auto c = std::dynamic_pointer_cast<Distinct<ID>>(condition);
        /*
        public:
        static const CONDITION_TYPE type = CONDITION_TYPE::DISTINCT;
        void print(std::ostream &ostr, const std::vector<Assignment<ID>*> &asgns) const override;
        void declareVariables(std::ostream &) const;

        Distinct(ID componentSlot) : componentSlot{componentSlot} {};

        const ID componentSlot;
         */
        // simple.addRule(distinct<std::string>("Colour"));
        // const ID componentSlot;

        // for all assignments in problem
        // this slot is distinct
        z3::expr_vector vars {context};
        for(const auto &asgn : problem.getAssignments())
            vars.push_back(slots.getVariable(asgn.first, c->componentSlot));

        z3::expr dis {context};
        if(!vars.empty())
            dis = z3::distinct(vars);


        return dis;

    }


    template<typename ID>
    void TranslatorZ3<ID>::print() const {

        std::cout << "START TZ3 TEST PRINT" << std::endl;

        sorts.print();

        slots.print();

        std::cout << "END TZ3 TEST PRINT" << std::endl;

    }


}


#endif //OMTSCHED_TRANSLATORZ3_H
