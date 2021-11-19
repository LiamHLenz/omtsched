//
// Created by hal on 18.11.21.
//

#include "TypeDialog.h"


TypeDialog::TypeDialog(wxWindow *parent, Problem &pr, wxWindowID id, const wxString &title, const wxPoint &position,
                                 const wxSize &size, long style) : wxDialog(parent, id, title, position, size, style), problem(pr) {


    wxFlexGridSizer *sizer_top = new wxFlexGridSizer(2);

    label_id = new wxStaticText(this, wxID_ANY, wxT("Type Name"));
    text_id = new wxTextCtrl(this, ID_TYPE_textID, "");


    wxGridSizer *sizer_comp = new wxGridSizer(2);
    sizer_comp->Add(label_id);
    sizer_comp->Add(text_id);

    wxBoxSizer *sizer_buttons = new wxBoxSizer(wxHORIZONTAL);

    button_save = new wxButton(this, ID_TYPE_buttonSave, wxT("Save"));
    button_cancel = new wxButton(this, ID_TYPE_buttonSave, wxT("Cancel"));

    sizer_buttons->Add(button_save);
    sizer_buttons->Add(button_cancel);


    sizer_top->Add(sizer_comp, 1, wxEXPAND);
    sizer_top->Add(sizer_buttons, 0);

    Bind(wxEVT_BUTTON, &TypeDialog::OnCancel, this, ID_TYPE_buttonCancel);
    Bind(wxEVT_BUTTON, &TypeDialog::OnSave, this, ID_TYPE_buttonSave);

    SetSizerAndFit(sizer_top);
    Centre();

}


void TypeDialog::OnSave(wxCommandEvent &event) {

    std::string id = text_id->GetLineText(0).ToStdString();

    problem.addComponentType(id);

    EndModal(0);

}

void TypeDialog::OnCancel(wxCommandEvent &event) {

    EndModal(1);
}
