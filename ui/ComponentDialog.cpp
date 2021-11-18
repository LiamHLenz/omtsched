//
// Created by Betrieb-PC on 16.11.2021.
//

#include "ComponentDialog.h"



ComponentDialog::ComponentDialog(wxWindow *parent, Problem &pr, wxWindowID id, const wxString &title, const wxPoint &position,
                             const wxSize &size, long style) : wxDialog(parent, id, title, position, size, style), problem(pr) {


    std::unique_ptr sizer_top = std::make_unique<wxFlexGridSizer>(2);

    // ---------------------------------------------------------------------------------
    //                              Input
    // ---------------------------------------------------------------------------------

    label_id = std::make_unique<wxStaticText>(this, wxID_ANY, wxT("ID"));
    text_id = std::make_unique<wxTextCtrl>(this, ID_COMP_textID, "");

    label_type = std::make_unique<wxStaticText>(this, wxID_ANY, wxT("Type"));
    combo_type = std::make_unique<wxComboBox>(this, ID_COMP_comboType);
    //combo_project = new wxComboBox(this, ID_comboProject, project_name, wxDefaultPosition, wxDefaultSize, project_strings.size(), project_strings.data());

    std::unique_ptr sizer_comp = std::make_unique<wxGridSizer>(2);
    sizer_comp->Add(label_id.get());
    sizer_comp->Add(text_id.get());

    sizer_comp->Add(label_type.get());
    sizer_comp->Add(combo_type.get());

    // ---------------------------------------------------------------------------------
    // -------------------------------- Layout -----------------------------------------
    // ---------------------------------------------------------------------------------

    auto sizer_buttons = std::make_unique<wxBoxSizer>(wxHORIZONTAL);

    button_save = std::make_unique<wxButton>(this, ID_COMP_buttonSave, wxT("Save"));
    button_cancel = std::make_unique<wxButton>(this, ID_COMP_buttonSave, wxT("Cancel"));

    sizer_buttons->Add(button_save.get());
    sizer_buttons->Add(button_cancel.get());


    sizer_top->Add(sizer_comp.get(), 1, wxEXPAND);
    sizer_top->Add(sizer_buttons.get(), 0);

    Bind(wxEVT_BUTTON, &ComponentDialog::OnCancel, this, ID_COMP_buttonCancel);
    Bind(wxEVT_BUTTON, &ComponentDialog::OnSave, this, ID_COMP_buttonSave);

    SetSizerAndFit(sizer_top.get());
    Centre();

}


void ComponentDialog::OnSave(wxCommandEvent &event) {

    std::string id = text_id->GetLineText(0).ToStdString();
    std::string type = combo_type->GetValue().ToStdString();

    problem.newComponent(id, type);

    EndModal(0);

}

void ComponentDialog::OnCancel(wxCommandEvent &event) {

    EndModal(1);
}
