//
// Created by hal on 18.11.21.
//

#ifndef OMTSCHED_ASSIGNMENTPANEL_H
#define OMTSCHED_ASSIGNMENTPANEL_H



#include <wx/wx.h>
#include <wx/dataview.h>
#include <memory>
#include "../Problem.h"

class AssignmentPanel : public wxPanel {

    using Problem = omtsched::Problem<std::string>;
    using Assignment = omtsched::Assignment<std::string>;

public:
    AssignmentPanel(wxWindow * parent, Problem &problem);

    void addAssignment(const Assignment &component);

protected:

    void OnAdd(wxCommandEvent& event);
    void OnDelete(wxCommandEvent& event);

    void OnEdit(wxCommandEvent& event);

    void refresh();

private:

    wxDataViewListCtrl *asgnctrl;
    Problem& problem;

    wxButton *button_add;
    wxButton *button_delete;

    wxButton *button_edit;

};

enum {
    ID_ASGN_Add = 2,
    ID_ASGN_Delete = 3,
    ID_ASGN_Edit = 4
};



#endif //OMTSCHED_ASSIGNMENTPANEL_H
