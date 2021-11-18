//
// Created by Betrieb-PC on 16.11.2021.
//

#include "ComponentPanel.h"
#include "ComponentDialog.h"

ComponentPanel::ComponentPanel(wxWindow *parent, Problem &problem) : wxPanel{parent}, problem{problem} {

    std::unique_ptr sizer_top = std::make_unique<wxBoxSizer>(wxVERTICAL);
    std::unique_ptr sizer_complist = std::make_unique<wxBoxSizer>(wxHORIZONTAL);
    std::unique_ptr sizer_typelist = std::make_unique<wxBoxSizer>(wxHORIZONTAL);

    typelistctrl = std::make_unique<wxDataViewListCtrl>(this, wxID_ANY, wxDefaultPosition, wxSize(1200,300));
    typelistctrl->AppendTextColumn("Type");

    sizer_typelist->Add(typelistctrl.get(), 1, wxEXPAND);

    complistctrl = std::make_unique<wxDataViewListCtrl>(this, wxID_ANY, wxDefaultPosition, wxSize(1200,300));
    complistctrl->AppendTextColumn("ID");
    complistctrl->AppendTextColumn("Type");
    complistctrl->AppendTextColumn("Groups");
    complistctrl->AppendTextColumn("Tags");

    sizer_complist->Add(complistctrl.get(), 1, wxEXPAND);
    sizer_top->Add(sizer_typelist.get(), 1, wxEXPAND);
    sizer_top->Add(sizer_complist.get(), 1, wxEXPAND);

    button_add = std::make_unique<wxButton>(this, ID_COMP_Add, wxString("&Add"));
    button_delete = std::make_unique<wxButton>(this, ID_COMP_Delete, wxString("&Delete"));
    button_edit_groups = std::make_unique<wxButton>(this, ID_COMP_EditG, wxString("&Edit Groups"));
    button_edit_tags = std::make_unique<wxButton>(this, ID_COMP_EditT, wxString("&Edit Tags"));

    Bind(wxEVT_BUTTON, &ComponentPanel::OnAdd, this, ID_COMP_Add);
    Bind(wxEVT_BUTTON, &ComponentPanel::OnDelete, this, ID_COMP_Delete);
    Bind(wxEVT_BUTTON, &ComponentPanel::OnEditGroups, this, ID_COMP_EditG);
    Bind(wxEVT_BUTTON, &ComponentPanel::OnEditTags, this, ID_COMP_EditT);

    std::unique_ptr sizer_buttons = std::make_unique<wxBoxSizer>(wxHORIZONTAL);
    sizer_buttons->Add(button_add.get());
    sizer_buttons->Add(button_edit_groups.get());
    sizer_buttons->Add(button_edit_tags.get());
    sizer_buttons->Add(button_delete.get());

    sizer_top->Add(sizer_buttons.get(), 0, wxALIGN_CENTER_HORIZONTAL);
    refresh();
    SetSizerAndFit(sizer_top.get());
}

void ComponentPanel::OnAdd(wxCommandEvent& event) {

    std::unique_ptr dialog = std::make_unique<ComponentDialog>(this, problem);
    dialog->ShowModal();
    refresh();

}

void ComponentPanel::OnDelete(wxCommandEvent& event) {
/*
    auto row = complistctrl->GetSelectedRow();
    std::string id = complistctrl->GetTextValue(row, 0).ToStdString(wxConvUTF8);
    problem.deleteComponent(id);
    refresh();
*/
}

void ComponentPanel::OnEditGroups(wxCommandEvent &event) {
/*
    std::string id = projectlistctrl->GetTextValue(row, 0).ToStdString(wxConvUTF8);
    std::unique_ptr dialog = std::make_unique<ComponentGroupDialog>(this, id);
    dialog->ShowModal();
    refresh();
    */
}

void ComponentPanel::OnEditTags(wxCommandEvent &event) {
/*
    std::string id = projectlistctrl->GetTextValue(row, 0).ToStdString(wxConvUTF8);
    std::unique_ptr dialog = std::make_unique<ComponentTagDialog>(this, id);
    dialog->ShowModal();
    refresh();
    */
}

void ComponentPanel::addComponentType(const ComponentType &type){

    wxVector<wxVariant> data;
    data.push_back(wxVariant(type.getID()));
    typelistctrl->AppendItem(data);
}


void ComponentPanel::addComponent(const Component &component) {

    wxVector<wxVariant> data;
    data.push_back(wxVariant(component.getID()));
    data.push_back(wxVariant(component.getType()));

    // Group string
    std::string groups = "";
    for(const std::string &group : component.getGroups())
        groups.append(", " + group);

    data.push_back(wxVariant(groups));

    // Tag string for non-zero tags
    std::string tags = "";
    for(const auto &[tag, val] : component.getTags()) {
        if(val != 0)
            tags.append(", " + tag + ": " + std::to_string(val));
    }

    data.push_back(wxVariant(tags));
    complistctrl->AppendItem(data);
}


void ComponentPanel::refresh() {

    // TODO: types

    // Components
    complistctrl->DeleteAllItems();

    for(std::string type : problem.getComponentTypes())
        for(const Component &component : problem.getComponents(type))
            addComponent(component);

}
