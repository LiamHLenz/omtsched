//
// Created by hal on 18.11.21.
//

#ifndef OMTSCHED_TYPEDIALOG_H
#define OMTSCHED_TYPEDIALOG_H

#include <wx/wx.h>
#include "../omtsched.h"

class TypeDialog : public wxDialog {

    using Problem = omtsched::Problem<std::string>;

public:
    TypeDialog(wxWindow * parent, Problem &problem, wxWindowID id = wxID_ANY, const wxString &title = "Project", const wxPoint &position = wxDefaultPosition, const wxSize &size = wxDefaultSize, long style = wxDEFAULT_DIALOG_STYLE);

private:

    Problem &problem;

    wxTextCtrl *text_id;
    wxStaticText *label_id;

    wxButton *button_save;
    wxButton *button_cancel;

    void OnSave(wxCommandEvent &event);
    void OnCancel(wxCommandEvent &event);

};


enum {

    ID_TYPE_textID,
    ID_TYPE_buttonSave,
    ID_TYPE_buttonCancel

};


#endif //OMTSCHED_TYPEDIALOG_H
