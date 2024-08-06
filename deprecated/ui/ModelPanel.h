//
// Created by hal on 19.11.21.
//

#ifndef OMTSCHED_MODELPANEL_H
#define OMTSCHED_MODELPANEL_H

#include <wx/wx.h>
#include <wx/dataview.h>
#include <wx/treelist.h>
#include "../Problem.h"

class ModelPanel : public wxPanel {

    using Problem = omtsched::Problem<std::string>;

public:
    ModelPanel(wxWindow * parent, Problem &problem);

protected:
    void OnGenerate(wxCommandEvent& event);

private:
    wxTreeListCtrl *listctrl;
    Problem& problem;
    wxButton *button_generate;

};

enum {
    ID_MODEL_Generate = 1
};

#endif //OMTSCHED_MODELPANEL_H
