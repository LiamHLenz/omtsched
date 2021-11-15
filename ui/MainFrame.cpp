//
// Created by hal on 12.11.21.
//

#include "MainFrame.h"

MyFrame::MyFrame()
        : wxFrame(NULL, wxID_ANY, "Hello World")
{
    menuFile = new wxMenu;

    menuFile->Append(ID_Hello, "&Hello...\tCtrl-H",
                     "Help string shown in status bar for this menu item");
    menuFile->AppendSeparator();
    menuFile->Append(wxID_EXIT);

    menuHelp = new wxMenu;
    menuHelp->Append(wxID_ABOUT);
    wxMenuBar *menuBar = new wxMenuBar;
    menuBar->Append(menuFile, "&File");
    menuBar->Append(menuHelp, "&Help");

    SetMenuBar( menuBar );
    CreateStatusBar();
    SetStatusText("Welcome to wxWidgets!");

    Bind(wxEVT_MENU, &MyFrame::OnHello, this, ID_Hello);
    Bind(wxEVT_MENU, &MyFrame::OnAbout, this, wxID_ABOUT);
    Bind(wxEVT_MENU, &MyFrame::OnExit, this, wxID_EXIT);

    // ---------------------------------------------------------------------------------


    wxBoxSizer *sizer = new wxBoxSizer(wxVERTICAL);
    notebook = new wxNotebook(this, wxID_ANY);
    sizer->Add(notebook, wxEXPAND);

    //notebook->AddPage( , "Overview");

    //notebook->AddPage( , "Components");

    //notebook->AddPage( , "Assignments");

    //SetClientSize(notebook->GetBestSize());


}


void MyFrame::OnExit(wxCommandEvent& event)
{
    Close(true);
}


void MyFrame::OnAbout(wxCommandEvent& event)
{
    wxMessageBox("This is a wxWidgets Hello World example",
                 "About Hello World", wxOK | wxICON_INFORMATION);
}


void MyFrame::OnHello(wxCommandEvent& event)
{
    wxLogMessage("Hello world from wxWidgets!");
}