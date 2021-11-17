//
// Created by Betrieb-PC on 16.11.2021.
//

#ifndef OMTSCHED_COMPONENTPANEL_H
#define OMTSCHED_COMPONENTPANEL_H


class ComponentPanel : public wxPanel {

public:
    ComponentPanel(wxWindow * parent, Project &project);
    ~ComponentPanel();

    void addComponentType();

    void addComponent();

protected:

        void OnAdd(wxCommandEvent& event);
        void OnDelete(wxCommandEvent& event);

        void OnEditGroups(wxCommandEvent& event);
        void OnEditTags(wxCommandEvent& event);

        void refresh();

private:

        std::unique_ptr<wxDataViewListCtrl> complistctrl;
        std::unique_ptr<wxDataViewListCtrl> typelistctrl;
        Problem& problem;

        std::unique_ptr<wxButton> button_add;
        std::unique_ptr<wxButton> button_delete;

        std::unique_ptr<wxButton> button_edit_groups;
        std::unique_ptr<wxButton> button_edit_tags;

        void addComponent(const Component<std::string> &component);
        void addType(const ComponentType<std::string> &type);

};

enum {
    ID_COMP_Add = 2,
    ID_COMP_Delete = 3,
    ID_COMP_EditG = 4,
    ID_COMP_EditT = 5
};


#endif //OMTSCHED_COMPONENTPANEL_H
