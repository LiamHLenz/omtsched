//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_COMPONENT_H
#define OMTSCHED_COMPONENT_H

#include <map>
#include <set>
#include "ComponentType.h"

namespace omtsched {

    template<typename ID>
    class Component {

    public:
        Component(const ID &id, const ComponentType<ID> &type) : ID{id}, type{type} {}
        //virtual const std::string componentType() const = 0;

        const ID getId() const;
        std::string getIDString() const;
        const std::map<ID, int> &getTags() const;
        const std::set<ID> &getGroups() const;

        void addGroup(const ID&);
        void removeGroup(const ID&);

        void setTag(const ID &, const int);

        const ComponentType<ID> &getType() const;

    private:
        ComponentType<ID> type;
        const ID id;
        std::map<ID, int> tags;
        std::set<ID> groups;
    };

    template<typename ID>
    const ComponentType<ID>&Component<ID>::getType() const {
        return type;
    }

    template<typename ID>
    const ID Component<ID>::getId() const {
        return id;
    }

    template<typename ID>
    const std::map<ID, int> &Component<ID>::getTags() const {
        return tags;
    }

    template<typename ID>
    const std::set<ID> &Component<ID>::getGroups() const {
        return groups;
    }

    template<typename ID>
    void Component<ID>::addGroup(const ID &id) {

        groups.insert(id);
    }

    template<typename ID>
    void Component<ID>::removeGroup(const ID &id) {

        groups.erase(id);
    }

    template<typename ID>
    void Component<ID>::setTag(const ID &id, const int val) {

        tags.at(id) = val;
    }

}

#endif //OMTSCHED_COMPONENT_H
