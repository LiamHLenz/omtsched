#ifndef OMTSCHED_OMTSCHED_H
#define OMTSCHED_OMTSCHED_H

#include <string>
#include "Task.h"
#include "Timeslot.h"

void hello();

template<typename ID, typename groupID, typename tagID>
bool addTask(const ID &id);

template<typename groupID>
void addGroup(const groupID&);

template <typename groupID>
void deleteGroup(const groupID&);

template <typename tagID>
void addTag(const tagID &id);

template <typename tagID>
void deleteTag(const tagID &id);

void saveEncoding();





#endif //OMTSCHED_OMTSCHED_H
