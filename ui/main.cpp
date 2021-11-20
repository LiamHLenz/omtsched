//
// Created by hal on 12.11.21.
//


#include <wx/wxprec.h>
#ifndef WX_PRECOMP
#include <wx/wx.h>
#endif

#include "MainFrame.h"
#include "../examples/zebra.cpp"

class MyApp : public wxApp
{
public:
    virtual bool OnInit();
};

IMPLEMENT_APP(MyApp);

bool MyApp::OnInit()
{
    if ( !wxApp::OnInit() )
        return false;

    omtsched::Problem<std::string> problem;
    getZebra(problem);
    //std::shared_ptr frame = std::make_shared<MainFrame>(problem);
    MainFrame *frame = new MainFrame(problem);
    frame->Show(true);
    return true;

}
