//
// Created by Betrieb-PC on 16.11.2021.
//

#ifndef OMTSCHED_COMPONENTPANEL_H
#define OMTSCHED_COMPONENTPANEL_H

#include <wx/wx.h>
#include <wx/dataview.h>
#include <memory>
#include "../Problem.h"

class ComponentPanel : public wxPanel {

    using Problem = omtsched::Problem<std::string>;
    using Component = omtsched::Component<std::string>;
    using ComponentType = omtsched::ComponentType<std::string>;

public:
    ComponentPanel(wxWindow * parent, Problem &problem);

    void addComponentType(const ComponentType &type);

    void addComponent(const Component &component);

protected:

        void OnAdd(wxCommandEvent& event);
        void OnDelete(wxCommandEvent& event);

        void OnEditGroups(wxCommandEvent& event);
        void OnEditTags(wxCommandEvent& event);

        void OnAddType(wxCommandEvent& event);
        void OnDeleteType(wxCommandEvent& event);

        void refresh();

private:

        wxDataViewListCtrl *complistctrl;
        wxDataViewListCtrl *typelistctrl;
        Problem& problem;

        wxButton *button_add;
        wxButton *button_delete;

        wxButton *button_edit_groups;
        wxButton *button_edit_tags;

        wxButton *button_addType;
        wxButton *button_deleteType;

};

enum {
    ID_COMP_Add = 2,
    ID_COMP_Delete = 3,
    ID_COMP_EditG = 4,
    ID_COMP_EditT = 5,
    ID_COMP_AddType = 6,
    ID_COMP_DeleteType = 7
};


#endif //OMTSCHED_COMPONENTPANEL_H
