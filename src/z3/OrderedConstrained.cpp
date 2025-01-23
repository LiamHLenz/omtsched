template<typename ID>
z3::expr TranslatorZ3<ID>::resolveGreater(const std::shared_ptr<Condition <ID>>& condition) {

    auto c = std::dynamic_pointer_cast<Greater<ID>>(condition);

    const ID& namedSlot = c->getNamedSlot();

    auto& greaterCond = c->subconditions.at(0);
    auto& smallerCond = c->subconditions.at(1);

    z3::expr_vector v(context);

    // limit search space: for all smaller => conditions must be false
    for (const auto& [id1, asgn1] : problem.getAssignments())
        for (const auto& [id2, asgn2] : problem.getAssignments())
            if (asgn1.getSlot(namedSlot).component < asgn2.getSlot(namedSlot).component)
                v.push_back((!(resolveCondition(greaterCond, &asgn1))) || !(resolveCondition(smallerCond, &asgn2)));

    return z3::mk_and(v);
}


template<typename ID>
z3::expr TranslatorZ3<ID>::resolveBlocked(const std::shared_ptr<Condition <ID>>& condition) {

    auto c = std::dynamic_pointer_cast<Blocked<ID>>(condition);

    // assuming total order (can be easily adjusted)
    // order assignments
    // needs fixed slot?

    // get (value of ordered, id)
    std::vector<std::pair<ID, ID>> order;
    order.reserve(problem.getAssignments().size());
    for (const auto& [id, asgn] : problem.getAssignments())
        order.push_back(std::make_pair(asgn.getSlot(c->getNamedSlot()).component, id));

    std::sort(order.begin(), order.end());

    z3::expr_vector v(context);


    //1. list all illegal combinations (urgh)
    //2. list all legal combinations (also bad)
    //3. two fulfill conditions => all in between fulfill condition
    //   add them all as implications....

    auto subcon = orC(c->subconditions);

    //forward iteration
    for (auto itf = order.begin(); itf != order.end() - 2; itf++)
        for (auto itb = order.end() - 1; itb > itf + 1; itb--)
            for (auto itbet = itf + 1; itbet != itb; itbet++) {
                auto if_first = resolveCondition(subcon, &problem.getAssignment(itf->second));
                auto if_second = resolveCondition(subcon, &problem.getAssignment(itb->second));
                auto then = resolveCondition(subcon, &problem.getAssignment(itbet->second));
                v.push_back(z3::implies(if_first && if_second, then));
            }



    // for every assignment: fulfills condition => previous or following fulfills condition (wrong!)
    /*for(auto it = order.begin(); it != order.end(); it++){

        z3::expr prev (context, Z3_mk_true(context));
        z3::expr next (context, Z3_mk_true(context));

        auto subcon = andC(c->subconditions);

        if(it != order.begin())
            prev = resolveCondition(subcon, &problem.getAssignment((it-1)->second));

        if((it+1) != order.end())
            next = resolveCondition(subcon, &problem.getAssignment((it+1)->second));

        z3::implies(resolveCondition(subcon, &problem.getAssignment(it->second)), prev && next);

    }
    */
    return z3::mk_and(v);

}