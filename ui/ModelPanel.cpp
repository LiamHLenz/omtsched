//
// Created by hal on 19.11.21.
//

#include "ModelPanel.h"
#include "../omtsched.h"

ModelPanel::ModelPanel(wxWindow *parent, Problem &problem) : wxPanel{parent}, problem{problem} {

    wxBoxSizer *sizer_top = new wxBoxSizer(wxHORIZONTAL);
    wxBoxSizer *sizer_list = new wxBoxSizer(wxVERTICAL);

    listctrl = new wxTreeListCtrl(this, wxID_ANY, wxDefaultPosition, wxSize(1200,300));

    listctrl->AppendColumn("Assignment");
    listctrl->AppendColumn("Slot");
    listctrl->AppendColumn("Component");

    sizer_list->Add(listctrl, 1, wxEXPAND);

    button_generate = new wxButton(this, ID_MODEL_Generate, wxString("&Generate"));
    Bind(wxEVT_BUTTON, &ModelPanel::OnGenerate, this, ID_MODEL_Generate);

    wxBoxSizer *sizer_buttons = new wxBoxSizer(wxVERTICAL);
    sizer_buttons->Add(button_generate);

    sizer_top->Add(sizer_list);
    sizer_top->Add(sizer_buttons);

    SetSizerAndFit(sizer_top);
}

void ModelPanel::OnGenerate(wxCommandEvent &event) {

    omtsched::TranslatorZ3<std::string> translatorZ3 {problem};
    translatorZ3.solve();

    if(!translatorZ3.isSAT())
        return;

    Model<std::string> model = translatorZ3.getModel();

}
