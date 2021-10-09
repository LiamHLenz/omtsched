//
// Created by hal on 04.09.21.
//

#ifndef OMTSCHED_AGENT_H
#define OMTSCHED_AGENT_H

#include "../Component.h"

namespace omtsched {

    template<typename ID>
    class Agent : public Component<ID> {
        public:
        Agent(const ID &id) : Component<ID>{id} {}
    };

}
#endif //OMTSCHED_AGENT_H
