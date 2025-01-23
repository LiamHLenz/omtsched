#include "TranslatorZ3.h"

template<typename ID>
const ID TranslatorZ3<ID>::getComponent(const z3::expr& variable) const {
    return sorts.getComponent(variable);
    //return components.getComponent(variable);
}

template<typename ID>
z3::expr TranslatorZ3<ID>::resolveComponentIs(const std::shared_ptr<Condition <ID>>& condition,
    const Assignment<ID>* asgn) {

    auto c = std::dynamic_pointer_cast<ComponentIs<ID>>(condition);
    const z3::expr& component = getConstant(c->component);
    const z3::expr& var = getVariable(asgn->getID(), c->componentSlot);
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
z3::expr TranslatorZ3<ID>::resolveSameComponent(const std::shared_ptr<Condition <ID>>& condition, const std::vector<Assignment<ID>*>& asgnComb) {

    auto c = std::dynamic_pointer_cast<SameComponent<ID>>(condition);

    z3::expr_vector equalities(context);
    for (auto it1 = asgnComb.begin(); it1 != asgnComb.end(); it1++)
        for (auto it2 = std::next(it1); it2 != asgnComb.end(); it2++) {

            const z3::expr& var1 = getVariable((*it1)->getID(), c->slot);
            const z3::expr& var2 = getVariable((*it2)->getID(), c->slot);
            equalities.push_back(var1 == var2);
        }
    return z3::mk_and(equalities);
}

template<typename ID>
z3::expr TranslatorZ3<ID>::resolveInGroup(const std::shared_ptr<Condition <ID>>& condition, const std::vector<Assignment<ID>*>& asgnComb) {

    auto c = std::dynamic_pointer_cast<InGroup<ID>>(condition);
    /*
     * InGroup(const ID &componentType, ID groupID) : slot{slot}, group{groupID} {}
        static const CONDITION_TYPE type = CONDITION_TYPE::IN_GROUP;
        const ID slot;
        const ID group;
     */

    const z3::expr& var = getVariable(asgnComb.at(0)->getID(), c->slot);
    // limits domain
    // get slot type
    const ID& type = asgnComb.at(0)->getSlot(c->slot).type;

    // std::map<ID, std::vector<Component<ID>>> components;
    z3::expr_vector equalities(context);
    for (const auto& component : this->problem.getComponents(type)) {

        if (component->inGroup(c->group)) {
            const z3::expr& comp = getConstant(component->getID());
            equalities.push_back(var == comp);
        }

    }
    return z3::mk_or(equalities);

}

