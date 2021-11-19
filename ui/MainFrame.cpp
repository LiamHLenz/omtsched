//
// Created by hal on 12.11.21.
//

#include "MainFrame.h"
#include <wx/filepicker.h>

MainFrame::MainFrame(Problem &problem)
        : wxFrame(NULL, wxID_ANY, "Hello World"), problem(problem)
{

    menuFile = new wxMenu();

    menuFile->Append(ID_Hello, "&Hello...\tCtrl-H",
                     "Help string shown in status bar for this menu item");
    menuFile->Append(ID_Load, "&Load");
    menuFile->Append(ID_Save, "&Save");
    menuFile->AppendSeparator();
    menuFile->Append(wxID_EXIT);

    menuHelp = new wxMenu();
    menuHelp->Append(wxID_ABOUT);

    menuBar = new wxMenuBar();
    menuBar->Append(menuFile, "&File");
    menuBar->Append(menuHelp, "&Help");

    SetMenuBar( menuBar );
    CreateStatusBar();
    SetStatusText("Welcome to wxWidgets!");

    Bind(wxEVT_MENU, &MainFrame::OnHello, this, ID_Hello);
    Bind(wxEVT_MENU, &MainFrame::OnAbout, this, wxID_ABOUT);
    Bind(wxEVT_MENU, &MainFrame::OnExit, this, wxID_EXIT);

    Bind(wxEVT_MENU, &MainFrame::OnLoad, this, ID_Load);
    Bind(wxEVT_MENU, &MainFrame::OnSave, this, ID_Save);

    // ---------------------------------------------------------------------------------


    sizer = new wxBoxSizer(wxVERTICAL);
    notebook = new wxNotebook(this, wxID_ANY);
    sizer->Add(notebook, wxEXPAND);


    //notebook->AddPage( , "Overview");

    componentPanel = new ComponentPanel(notebook, problem);
    notebook->AddPage(componentPanel, "Components");

    assignmentPanel = new AssignmentPanel(notebook, problem);
    notebook->AddPage(assignmentPanel, "Assignments");

    //refresh();
    SetSizerAndFit(sizer);

}


void MainFrame::OnExit(wxCommandEvent& event)
{
    Close(true);
}


void MainFrame::OnAbout(wxCommandEvent& event)
{
    wxMessageBox("This is a wxWidgets Hello World example",
                 "About Hello World", wxOK | wxICON_INFORMATION);
}


void MainFrame::OnHello(wxCommandEvent& event)
{
    wxLogMessage("Hello world from wxWidgets!");
}

void MainFrame::OnLoad(wxCommandEvent &event) {
    //TODO: load from smt2 file
    //wxFileDialog *fileDialog = new wxFileDialog(this, wxID_ANY);
}

void MainFrame::OnSave(wxCommandEvent &event) {
    //TODO: save to smt2 file
}
