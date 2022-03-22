//
// Created by hal on 12.12.21.
//

#include "../omtsched.h"
#include "zebra.cpp"

int main() {

    omtsched::Problem<std::string> problem;
    getZebra(problem);
    omtsched::TranslatorZ3<std::string> translatorZ3(problem);
    translatorZ3.print();
    //translatorZ3.solve();
    //omtsched::Model<std::string> model = translatorZ3.getModel();
    //model.print(std::cout);
    
    /* //copied example for testing
    using namespace z3;
    std::cout << "enumeration sort example\n";
    context ctx;
    const char * enum_names[] = { "a", "b", "c" };
    func_decl_vector enum_consts(ctx);
    func_decl_vector enum_testers(ctx);
    sort s = ctx.enumeration_sort("enumT", 3, enum_names, enum_consts, enum_testers);
    // enum_consts[0] is a func_decl of arity 0.
    // we convert it to an expression using the operator()
    expr a = enum_consts[0]();
    expr b = enum_consts[1]();
    expr x = ctx.constant("x", s);
    //expr test = (x==a);
    //std::cout << "1: " << test << std::endl;
    tactic qe(ctx, "ctx-solver-simplify");
    goal g(ctx);
    //g.add(test);
    expr res(ctx);
    apply_result result_of_elimination = qe.apply(g);
    goal result_goal = result_of_elimination[0];
    std::cout << "2: " << result_goal.as_expr() << std::endl;
    solver sv(ctx);
    sv.add(x == a || x == b);
    sv.check();
    model m = sv.get_model();
    std::cout << "m: " << m << std::endl;
    std::cout << "x: " << m.eval(x) << std::endl;
    for(int i = 0; i < m.size(); i++) {
    
        func_decl comp = m[i];
        std::cout << "Var: " << comp.name() << "intr: " << m.get_const_interp(comp) << std::endl;
    
    }
    */
}