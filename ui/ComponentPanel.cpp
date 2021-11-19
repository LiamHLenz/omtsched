//
// Created by Betrieb-PC on 16.11.2021.
//

#include "ComponentPanel.h"
#include "ComponentDialog.h"
#include "TypeDialog.h"

ComponentPanel::ComponentPanel(wxWindow *parent, Problem &problem) : wxPanel{parent}, problem{problem} {

    wxBoxSizer *sizer_top = new wxBoxSizer(wxVERTICAL);
    wxBoxSizer *sizer_complist = new wxBoxSizer(wxHORIZONTAL);
    wxBoxSizer *sizer_typelist = new wxBoxSizer(wxHORIZONTAL);

    typelistctrl = new wxDataViewListCtrl(this, wxID_ANY, wxDefaultPosition, wxSize(1200,300));
    typelistctrl->AppendTextColumn("Type");

    button_addType = new wxButton(this, ID_COMP_AddType, wxString("&Add"));
    button_deleteType = new wxButton(this, ID_COMP_Delete, wxString("&Delete"));
    sizer_typelist->Add(typelistctrl, 1, wxEXPAND);

    wxBoxSizer *sizer_type_buttons = new wxBoxSizer(wxVERTICAL);
    sizer_type_buttons->Add(button_addType);
    sizer_type_buttons->Add(button_deleteType);
    sizer_typelist->Add(sizer_type_buttons);

    Bind(wxEVT_BUTTON, &ComponentPanel::OnAddType, this, ID_COMP_AddType);
    Bind(wxEVT_BUTTON, &ComponentPanel::OnDeleteType, this, ID_COMP_DeleteType);

    complistctrl = new wxDataViewListCtrl(this, wxID_ANY, wxDefaultPosition, wxSize(1200,300));
    complistctrl->AppendTextColumn("ID");
    complistctrl->AppendTextColumn("Type");
    complistctrl->AppendTextColumn("Groups");
    complistctrl->AppendTextColumn("Tags");

    sizer_complist->Add(complistctrl, 1, wxEXPAND);
    sizer_top->Add(sizer_typelist, 1, wxEXPAND);

    button_add = new wxButton(this, ID_COMP_Add, wxString("&Add"));
    button_delete = new wxButton(this, ID_COMP_Delete, wxString("&Delete"));
    button_edit_groups = new wxButton(this, ID_COMP_EditG, wxString("&Edit Groups"));
    button_edit_tags = new wxButton(this, ID_COMP_EditT, wxString("&Edit Tags"));

    Bind(wxEVT_BUTTON, &ComponentPanel::OnAdd, this, ID_COMP_Add);
    Bind(wxEVT_BUTTON, &ComponentPanel::OnDelete, this, ID_COMP_Delete);
    Bind(wxEVT_BUTTON, &ComponentPanel::OnEditGroups, this, ID_COMP_EditG);
    Bind(wxEVT_BUTTON, &ComponentPanel::OnEditTags, this, ID_COMP_EditT);


    wxBoxSizer *sizer_buttons = new wxBoxSizer(wxVERTICAL);
    sizer_buttons->Add(button_add);
    sizer_buttons->Add(button_edit_groups);
    sizer_buttons->Add(button_edit_tags);
    sizer_buttons->Add(button_delete);

    sizer_complist->Add(sizer_buttons, 0, wxALIGN_CENTER_HORIZONTAL);
    sizer_top->Add(sizer_complist);

    refresh();
    SetSizerAndFit(sizer_top);
}

void ComponentPanel::OnAdd(wxCommandEvent& event) {

    ComponentDialog *dialog = new ComponentDialog(this, problem);
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

void ComponentPanel::OnAddType(wxCommandEvent &event) {

    TypeDialog *dialog = new TypeDialog(this, problem);
    dialog->ShowModal();
    refresh();
}

void ComponentPanel::OnDeleteType(wxCommandEvent &event) {
/*
    auto row = complistctrl->GetSelectedRow();
    std::string id = complistctrl->GetTextValue(row, 0).ToStdString(wxConvUTF8);
    problem.deleteComponentType(id);
    refresh();*/
}

void ComponentPanel::refresh() {

    typelistctrl->DeleteAllItems();
    complistctrl->DeleteAllItems();

    for(const std::string &type : problem.getComponentTypes()) {

        wxVector<wxVariant> data;
        data.push_back(wxVariant(type));
        typelistctrl->AppendItem(data);

        for(const Component &component : problem.getComponents(type))
            addComponent(component);
    }

}
