//
// Created by admin on 25.08.2021.
//

#ifndef OMTSCHED_COMPONENT_H
#define OMTSCHED_COMPONENT_H

#include <map>
#include <set>
#include <memory>
#include "ComponentType.h"

namespace omtsched {

    template<typename ID>
    class Component {

    public:
        Component(const ID &id, const ID &type) : id{id}, type{type} {}
        virtual ~Component() = default;
        //virtual const std::string componentType() const = 0;

        const ID getID() const;
        const ID getType() const;

        const std::map<ID, int> &getTags() const;
        const std::set<ID> &getGroups() const;

        void addGroup(const ID&);
        void removeGroup(const ID&);
        
        bool inGroup(const ID &group) const;

        void setTag(const ID &, const int);

    private:
        const ID id;
        const ID type;
        std::map<ID, int> tags;
        std::set<ID> groups;
    };


    template<typename ID>
    const ID Component<ID>::getID() const {
        return id;
    }

    template<typename ID>
    const ID Component<ID>::getType() const {
        return type;
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
    bool Component<ID>::inGroup(const ID &group) const {
        return groups.find(group) != groups.end();
    }

    template<typename ID>
    void Component<ID>::setTag(const ID &id, const int val) {

        tags.at(id) = val;
    }

    template<typename ID>
    class OrderedComponent : public Component<ID> {

        public:

            OrderedComponent(const ID &id, const ID &type, const int &point) : Component<ID>{id, type}, point{point} {}

            friend bool operator<(const OrderedComponent<ID> &lhs, const OrderedComponent<ID> &rhs);
        private:
            int point;
        };

    template<typename ID>
    bool operator<(const OrderedComponent<ID> &lhs, const OrderedComponent<ID> &rhs) { return lhs.point < rhs.point; }

}

#endif //OMTSCHED_COMPONENT_H
