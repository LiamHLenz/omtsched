//
// Created by hal on 13.12.21.
//

#ifndef OMTSCHED_MAPS_H
#define OMTSCHED_MAPS_H

#include <z3.h>
#include <z3++.h>

namespace omtsched {

    
    template<typename ID>
    struct ComponentMap {
    public:
        ComponentMap(const Problem<ID> &problem);

        const z3::expr &getVariable(const ID &) const;

        const ID &getComponent(const z3::expr &) const;
        
        void set(const ID &, const std::string &, const z3::expr &);

    private:
        const Problem<ID> &problem;
        std::map<ID, z3::expr> variableMap;
        std::map<std::string, ID> idMap;
    };
    
    template<typename ID>
    ComponentMap<ID>::ComponentMap(const Problem<ID> &problem) : problem{problem} {
        /*
        int typeCount = 0;
        for(const ID &type : problem.getComponentTypes()){
            
            int compCount = 0;
            
            for(const Component<ID> &component : problem.getComponents(type)){
                
                std::string name = "s" + std::to_string(typeCount) + "c" + std::to_string(compCount);
                nameMap.emplace(component.getID(), name);
                idMap.emplace(name, component.getID());
                compCount++;
            }
            typeCount++;
        }*/
                
    }
    
    template<typename ID>
    const z3::expr &ComponentMap<ID>::getVariable(const ID &id) const {
        return idMap.at(id);
    }

    template<typename ID>
    const ID &ComponentMap<ID>::getComponent(const z3::expr &name) const {
        return variableMap.at(name);
    }

    template<typename ID>
    void ComponentMap<ID>::set(const ID &id, const std::string &name, const z3::expr &expr) {
        variableMap.emplace(id, expr);
        idMap.emplace(name, id);
    }



    /*
    * z3::sort does not define an order so boost::bimap cannot be used directly
    * This is a simple wrapper to circumvent that issue.
    */
    template<typename ID>
    struct SortMap {

    public:
        SortMap(z3::context &context, ComponentMap<ID>& cmp) : context{context}, componentMap{cmp} {};
        const z3::sort &getSort(const ID &type) const;
        //const ID &getType(const z3::sort &sort) const;
        //void set(const ID &type, const std::string &name);
        void set(const ID &type, const std::string &name, const std::vector<std::shared_ptr<Component<ID>>> &names, std::vector<z3::func_decl_vector> &enum_consts, std::vector<z3::func_decl_vector> &enum_testers);
        //void remove(const z3::sort &sort);
        //void remove(const ID &type);

    private:
        z3::context &context;
        ComponentMap<ID> &componentMap;
        std::map<ID, z3::sort> sortMap;
        //std::map<std::string, ID> componentMap;
    };

    template<typename ID>
    const z3::sort &SortMap<ID>::getSort(const ID &type) const {
        return sortMap.at(type);
    }

    //template<typename ID>
    //const ID &SortMap<ID>::getType(const z3::sort &sort) const {
    //    return componentMap.at(sort);
    //}

    //template<typename ID>
    //void SortMap<ID>::set(const ID &type, std::vector<std::string> &names) {
        //sortMap.emplace(type, context.uninterpreted_sort(name.c_str()));
        //componentMap.emplace(name, type);
        // "Return an enumeration sort: enum_names[0], ..., enum_names[n-1]. cs and ts are output parameters. 
        // The method stores in cs the constants corresponding to the enumerated 
        // elements, and in ts the predicates for testing if terms of the enumeration 
        // sort correspond to an enumeration." 
        //z3::func_decl_vector enum_consts(context);
        //z3::func_decl_vector enum_testers(context);
        //sort s = ctx.enumeration_sort("enumT", 3, enum_names, enum_consts, enum_testers);
        //context.enumeration_sort(name, names.size(), names.data(), enum_consts, enum_testers);
    //}

    template<typename ID>
    void SortMap<ID>::set(const ID &type, const std::string &name, const std::vector<std::shared_ptr<Component<ID>>> &names, std::vector<z3::func_decl_vector> &enum_consts, std::vector<z3::func_decl_vector> &enum_testers) {
        
        assert(!names.empty() && "Attempting to create empty sort");
        
        const char * enum_names[names.size()];
        for(int i = 0; i < names.size(); i++) {
            std::string comp_name = name + "_c" + std::to_string(i);
            
            enum_names[i] = comp_name.data();
            
        }
        
        
        z3::sort sort = context.enumeration_sort(name.data(), names.size(), enum_names, enum_consts.back(), enum_testers.back());
        sortMap.emplace(type, sort);    
        
        for(int i = 0; i < names.size(); i++) {
            std::string comp_name = name + "_c" + std::to_string(i);
            
            z3::expr expr = enum_consts.back()[i]();
            componentMap.set(names.at(i)->getID(), comp_name, expr);
            
        } 
    }

    //template<typename ID>
    //void SortMap<ID>::remove(const z3::sort &sort) {
    //    const ID &id = componentMap.at(sort);
    //    sortMap.erase(id);
    //    componentMap.erase(sort.name().str());
    //}

    /*template<typename ID>
    void SortMap<ID>::remove(const ID &type) {
        //const z3::sort &sort = sortMap.at(type);
        sortMap.erase(type);
        //componentMap.erase(sort.name().str());
    }*/


 

    /*
    template<typename ID>
    struct ComponentMap {
    public:
        ComponentMap(z3::context &context) : context{context} {};

        const z3::expr &getVariable(const ID &) const;

        const ID &getComponent(const z3::expr &) const;

        void set(const ID &id, const std::string &varName, const z3::sort &sort);

        void remove(const ID &);

        void remove(const z3::expr &);

    private:
        z3::context &context;
        std::map<ID, z3::expr> variableMap;
        std::map<unsigned, ID> componentMap;
    };

    template<typename ID>
    const z3::expr &ComponentMap<ID>::getVariable(const ID &id) const {
        return variableMap.at(id);
    }

    template<typename ID>
    const ID &ComponentMap<ID>::getComponent(const z3::expr &var) const {
        return componentMap.at(var.id());
    }

    template<typename ID>
    void ComponentMap<ID>::set(const ID &id, const std::string &varName, const z3::sort &sort) {
        variableMap.emplace(std::make_pair(id, context.constant(varName.c_str(), sort)));
        componentMap.emplace(variableMap.at(id).id(), id);
    }

    template<typename ID>
    void ComponentMap<ID>::remove(const ID &id) {
        const z3::expr &var = variableMap.at(id);
        componentMap.erase(var.id());
        variableMap.erase(id);
    }

    template<typename ID>
    void ComponentMap<ID>::remove(const z3::expr &var) {
        const ID &id = componentMap.at(var.get_string());
        componentMap.erase(var.id());
        variableMap.erase(id);
    }

    */

    template<typename ID>
    struct SlotMap {

    public:
        SlotMap(z3::context &context) : context{context} {};

        const z3::expr &getVariable(const ID &, const ID &) const;

        const std::pair<ID, ID> &getSlot(const z3::expr &) const;

        void set(const ID &assignment, const ID &slot, const z3::sort &type, const std::string &name);

        void remove(const ID &, const ID &);

        void remove(const z3::expr &);

    private:

        z3::context &context;
        std::map<std::pair<ID, ID>, z3::expr> variableMap;
        std::map<std::string, std::pair<ID, ID>> slotMap;

    };

    template<typename ID>
    const z3::expr &SlotMap<ID>::getVariable(const ID &assignment, const ID &slot) const {
        return variableMap.at(std::make_pair(assignment, slot));
    }

    template<typename ID>
    const std::pair<ID, ID> &SlotMap<ID>::getSlot(const z3::expr &expr) const {
        return slotMap.at(expr.get_string());
    }

    template<typename ID>
    void SlotMap<ID>::set(const ID &assignment, const ID &slot, const z3::sort &type, const std::string &name) {

        variableMap.emplace(std::make_pair(std::make_pair(assignment, slot), context.constant(name.c_str(), type)));
        slotMap.emplace(name, std::make_pair(assignment, slot));
    }

    template<typename ID>
    void SlotMap<ID>::remove(const ID &assignment, const ID &slot) {
        const z3::expr &variable = variableMap.at(std::make_pair(assignment, slot));
        slotMap.erase(variable.get_string());
        variableMap.erase(std::make_pair(assignment, slot));
    }

    template<typename ID>
    void SlotMap<ID>::remove(const z3::expr &expr) {
        const std::pair<ID, ID> &ids = slotMap.at(expr.get_string());
        variableMap.erase(ids);
        slotMap.erase(expr.get_string());
    }

}

#endif //OMTSCHED_MAPS_H
