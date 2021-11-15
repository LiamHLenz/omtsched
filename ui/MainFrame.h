//
// Created by hal on 12.11.21.
//

#ifndef OMTSCHED_MAINFRAME_H
#define OMTSCHED_MAINFRAME_H

#include <wx/wx.h>
#include <wx/notebook.h>

class MyFrame : public wxFrame
{
public:
    MyFrame();
private:
    void OnHello(wxCommandEvent& event);
    void OnExit(wxCommandEvent& event);
    void OnAbout(wxCommandEvent& event);

    wxMenu *menuFile;
    wxMenu *menuHelp;

    wxPanel *m_panel; // Panel containing notebook and other controls
    wxNotebook *notebook;
};
enum
{
    ID_Hello = 1
};


#endif //OMTSCHED_MAINFRAME_H
