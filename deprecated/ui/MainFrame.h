//
// Created by hal on 12.11.21.
//

#ifndef OMTSCHED_MAINFRAME_H
#define OMTSCHED_MAINFRAME_H

#include <wx/wx.h>
#include <wx/notebook.h>
#include <memory>
#include "ComponentPanel.h"
#include "AssignmentPanel.h"
#include "ModelPanel.h"

class MainFrame : public wxFrame {

    using Problem = omtsched::Problem<std::string>;

public:
    MainFrame(Problem &problem);
private:
    void OnHello(wxCommandEvent& event);
    void OnExit(wxCommandEvent& event);
    void OnAbout(wxCommandEvent& event);

    void OnLoad(wxCommandEvent& event);
    void OnSave(wxCommandEvent& event);

    wxMenu *menuFile;
    wxMenu *menuHelp;
    wxMenuBar *menuBar;

    wxBoxSizer *sizer;

    wxPanel *m_panel; // Panel containing notebook and other controls
    wxNotebook *notebook;

    ComponentPanel *componentPanel;
    AssignmentPanel *assignmentPanel;
    ModelPanel *modelPanel;

    Problem &problem;
};
enum
{
    ID_Hello = 1,
    ID_Load = 2,
    ID_Save = 3
};


#endif //OMTSCHED_MAINFRAME_H
