//
// Created by hal on 18.11.21.
//

#include "AssignmentPanel.h"
#include <wx/wx.h>


AssignmentPanel::AssignmentPanel(wxWindow *parent, Problem &problem) : wxPanel{parent}, problem{problem} {

    wxBoxSizer *sizer_top = new wxBoxSizer(wxHORIZONTAL);
    wxBoxSizer *sizer_list = new wxBoxSizer(wxHORIZONTAL);

    asgnctrl = new wxDataViewListCtrl(this, wxID_ANY, wxDefaultPosition, wxSize(1200,300));
    asgnctrl->AppendTextColumn("ID");
    asgnctrl->AppendTextColumn("Optional");
    asgnctrl->AppendTextColumn("Slots");
    sizer_list->Add(asgnctrl);

    button_add = new wxButton(this, ID_ASGN_Add, wxString("&Add"));
    button_delete = new wxButton(this, ID_ASGN_Delete, wxString("&Delete"));
    button_edit = new wxButton(this, ID_ASGN_Edit, wxString("&Edit"));

    Bind(wxEVT_BUTTON, &AssignmentPanel::OnAdd, this, ID_ASGN_Add);
    Bind(wxEVT_BUTTON, &AssignmentPanel::OnDelete, this, ID_ASGN_Delete);
    Bind(wxEVT_BUTTON, &AssignmentPanel::OnEdit, this, ID_ASGN_Edit);


    wxBoxSizer *sizer_buttons = new wxBoxSizer(wxVERTICAL);
    sizer_buttons->Add(button_add);
    sizer_buttons->Add(button_edit);
    sizer_buttons->Add(button_delete);

    sizer_top->Add(sizer_list);
    sizer_top->Add(sizer_buttons);

    refresh();
    SetSizerAndFit(sizer_top);
}

void AssignmentPanel::OnAdd(wxCommandEvent& event) {
/*
    AssignmentDialog *dialog = new AssignmentDialog(this, problem);
    dialog->ShowModal();
    refresh();
*/
}

void AssignmentPanel::OnDelete(wxCommandEvent& event) {
/*
    auto row = complistctrl->GetSelectedRow();
    std::string id = complistctrl->GetTextValue(row, 0).ToStdString(wxConvUTF8);
    problem.deleteAssignment(id);
    refresh();
*/
}

void AssignmentPanel::OnEdit(wxCommandEvent &event) {
/*
    std::string id = projectlistctrl->GetTextValue(row, 0).ToStdString(wxConvUTF8);
    std::unique_ptr dialog = std::make_unique<AssignmentDialog>(this, id);
    dialog->ShowModal();
    refresh();
    */
}

void AssignmentPanel::addAssignment(const Assignment &asgn){

    wxVector<wxVariant> data;
    data.push_back(wxVariant(asgn.getID()));

    if(asgn.isOptional())
        data.push_back(wxVariant(std::to_string(asgn.getWeight())));
    else
        data.push_back(wxVariant("-"));

    std::string slots = "";
    for(const auto &[id, slot] : asgn.getComponentSlots())
        slots.append(" " + id);

    data.push_back(wxVariant(slots));

    asgnctrl->AppendItem(data);
}


void AssignmentPanel::refresh() {

    asgnctrl->DeleteAllItems();

    for(const auto &[id, assignment] : problem.getAssignments())
        addAssignment(assignment);

}
