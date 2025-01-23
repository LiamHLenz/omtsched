template<typename ID>
z3::expr TranslatorZ3<ID>::resolveDistinct(const std::shared_ptr<Condition <ID>>& condition) {

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
    z3::expr_vector vars{ context };
    for (const auto& asgn : problem.getAssignments())
        vars.push_back(slots.getVariable(asgn.first, c->componentSlot));

    z3::expr dis{ context };
    if (!vars.empty())
        dis = z3::distinct(vars);


    return dis;

}


