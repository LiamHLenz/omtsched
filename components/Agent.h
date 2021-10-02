//
// Created by hal on 04.09.21.
//

#ifndef OMTSCHED_AGENT_H
#define OMTSCHED_AGENT_H

#include "../Component.h"

namespace omtsched {

    template<class ComponentID, class TagID, class GroupID>
    class Agent : public Component<ComponentID, TagID, GroupID> {
        public:
        Agent(const ComponentID &id) : Component<ComponentID, TagID, GroupID>{id} {}
    };

}
#endif //OMTSCHED_AGENT_H
