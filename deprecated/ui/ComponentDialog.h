//
// Created by Betrieb-PC on 16.11.2021.
//

#ifndef OMTSCHED_COMPONENTDIALOG_H
#define OMTSCHED_COMPONENTDIALOG_H

#include <wx/wx.h>
#include "../omtsched.h"

class ComponentDialog : public wxDialog {

using Problem = omtsched::Problem<std::string>;

public:
    ComponentDialog(wxWindow * parent, Problem &problem, wxWindowID id = wxID_ANY, const wxString &title = "Project", const wxPoint &position = wxDefaultPosition, const wxSize &size = wxDefaultSize, long style = wxDEFAULT_DIALOG_STYLE);

private:

    Problem &problem;

    wxTextCtrl *text_id;
    wxStaticText *label_id;

    wxComboBox *combo_type;
    wxStaticText *label_type;

    wxButton *button_save;
    wxButton *button_cancel;

    void OnSave(wxCommandEvent &event);
    void OnCancel(wxCommandEvent &event);

};


enum {

    ID_COMP_textID,
    ID_COMP_comboType,
    ID_COMP_buttonSave,
    ID_COMP_buttonCancel

};


#endif //OMTSCHED_COMPONENTDIALOG_H
