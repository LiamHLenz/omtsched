//
// Created by hal on 12.11.21.
//

#include "MainFrame.h"
#include <wx/filepicker.h>
#include <wx/wfstream.h>
#include <fstream>

MainFrame::MainFrame(Problem &problem)
        : wxFrame(NULL, wxID_ANY, "omtsched"), problem(problem)
{

    menuFile = new wxMenu();

    //menuFile->Append(ID_Load, "&Load");
    //menuFile->Append(ID_Save, "&Save");
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

    Bind(wxEVT_MENU, &MainFrame::OnAbout, this, wxID_ABOUT);
    Bind(wxEVT_MENU, &MainFrame::OnExit, this, wxID_EXIT);

    //Bind(wxEVT_MENU, &MainFrame::OnLoad, this, ID_Load);
    //Bind(wxEVT_MENU, &MainFrame::OnSave, this, ID_Save);

    // ---------------------------------------------------------------------------------


    sizer = new wxBoxSizer(wxVERTICAL);
    notebook = new wxNotebook(this, wxID_ANY);
    sizer->Add(notebook, wxEXPAND);


    //notebook->AddPage( , "Overview");

    componentPanel = new ComponentPanel(notebook, problem);
    notebook->AddPage(componentPanel, "Components");

    assignmentPanel = new AssignmentPanel(notebook, problem);
    notebook->AddPage(assignmentPanel, "Assignments");

    modelPanel = new ModelPanel(notebook, problem);
    notebook->AddPage(modelPanel, "Model");

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
    //TODO: load from xml or plain file
    //TODO: load from smt2 file
    //wxFileDialog *fileDialog = new wxFileDialog(this, wxID_ANY);
}

void MainFrame::OnSave(wxCommandEvent &event) {
    //TODO: load from xml or plain file
    //TODO: save to smt2 file
    /*
    wxFileDialog fileDialog(this, _("Save file"), "", "",
                            "smt2 files (*.smt2)|*.smt2", wxFD_SAVE|wxFD_OVERWRITE_PROMPT);
    if(fileDialog.ShowModal() == wxID_CANCEL)
        return;

    wxFileOutputStream outStream(fileDialog.GetPath());
    if(!outStream.IsOk()){
        wxLogError("Error saving to file %s", fileDialog.GetPath());
        return;
    }

    //TODO: switching between two streams for saving - bad idea?
    std::string path = fileDialog.GetPath().ToStdString();
    outStream.Close();

    std::fstream fstream (path);
    if(!fstream.good()){
        wxLogError("Error saving to created file");
        return;
    }

    problem.print(fstream);
    fstream.close(); */

}
