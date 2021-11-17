//
// Created by Betrieb-PC on 16.11.2021.
//

#ifndef OMTSCHED_COMPONENTDIALOG_H
#define OMTSCHED_COMPONENTDIALOG_H


class ComponentDialog : public wxDialog {

public:
    ComponentDialog(wxWindow * parent, Problem &problem, wxWindowID id = wxID_ANY, const wxString &title = "Project", const wxPoint &position = wxDefaultPosition, const wxSize &size = wxDefaultSize, long style = wxDEFAULT_DIALOG_STYLE);

private:

    Problem &problem;

    std::unique_ptr<wxTextCtrl> text_id;
    std::unique_ptr<wxStaticText> label_id;

    std::unique_ptr<wxComboBox> combo_type;
    std::unique_ptr<wxStaticText> label_type;

    std::unique_ptr<wxButton> button_save;
    std::unique_ptr<wxButton> button_cancel;

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
