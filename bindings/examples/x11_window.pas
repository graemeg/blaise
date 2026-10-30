{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ x11_window — a complete Xlib GUI application on the generated x11
  binding.  This is the classic Xlib tutorial program, and it exercises
  every mechanism a toolkit port needs:

    * connect, create + title a window, select an event mask
    * the WM_DELETE_WINDOW protocol (XInternAtom + XSetWMProtocols)
    * a GC and real drawing (XFillRectangle, XDrawRectangle,
      XDrawString) on Expose
    * the XEvent union via the generated typed accessors
      (XEvent_type_, XEvent_xkey, XEvent_xbutton, XEvent_xclient)
    * keysym constants (XK_Escape / XK_q_) via XLookupKeysym
    * clean shutdown through the window manager's close button,
      Escape/q, or a self-sent ClientMessage

  Build (from the repo root):

    compiler/target/blaise --source bindings/examples/x11_window.pas \
      --output /tmp/x11_window \
      --unit-path bindings/src/main/pascal \
      --unit-path stdlib/src/main/pascal

  Run it and click around; close with Escape, 'q', or the WM button.
  Pass --autoclose to have the program close ITSELF after the first
  Expose by sending its own WM_DELETE_WINDOW ClientMessage — the same
  code path the window manager uses — so the full event loop can be
  exercised unattended (CI, headless smoke tests). }

program x11_window;

uses
  x11;

const
  WinWidth = 420;
  WinHeight = 300;

var
  Dpy: PDisplay;
  Scr: Int32;
  Win: Window;
  Gfx: GC;
  WmDelete: Atom;
  Ev: XEvent;
  Key: KeySym;
  Running: Boolean;
  AutoClose: Boolean;
  Exposed: Boolean;
  Clicks: Int;
  Msg: string;

procedure DrawContents;
begin
  XSetForeground(Dpy, Gfx, XBlackPixel(Dpy, Scr));
  XDrawString(Dpy, Win, Gfx, 20, 40,
    PChar('Hello from Blaise!'), 18);
  XDrawString(Dpy, Win, Gfx, 20, 64,
    PChar('This window is driven by the generated x11 binding.'), 52);
  XDrawString(Dpy, Win, Gfx, 20, 88,
    PChar('Click anywhere; press Escape or q to quit.'), 42);
  { A filled bar along the bottom, plus its outline. }
  XFillRectangle(Dpy, Win, Gfx, 20, WinHeight - 60, 120, 30);
  XDrawRectangle(Dpy, Win, Gfx, 160, WinHeight - 60, 120, 29);
end;

procedure SendSelfClose;
var
  CloseEv: XEvent;
  M: PXClientMessageEvent;
begin
  { Close the same way the window manager would: a ClientMessage
    carrying WM_DELETE_WINDOW.  Field access goes through the typed
    union accessor; data.l[0] lives in the raw storage of the lifted
    data union (8-byte slots, so raw[0] IS l[0]). }
  M := XEvent_xclient(CloseEv);
  M^.type_ := ClientMessage;
  M^.window := Win;
  M^.message_type := XInternAtom(Dpy, PChar('WM_PROTOCOLS'), 1);
  M^.format := 32;
  M^.data.raw[0] := UInt64(WmDelete);
  XSendEvent(Dpy, Win, 0, NoEventMask, @CloseEv);
  XFlush(Dpy);
end;

begin
  AutoClose := (ParamCount() >= 1) and (ParamStr(1) = '--autoclose');

  Dpy := XOpenDisplay(nil);
  if Dpy = nil then
  begin
    WriteLn('x11_window: cannot open display');
    Halt(1);
  end;
  Scr := XDefaultScreen(Dpy);

  Win := XCreateSimpleWindow(Dpy, XDefaultRootWindow(Dpy),
    100, 100, WinWidth, WinHeight, 1,
    XBlackPixel(Dpy, Scr), XWhitePixel(Dpy, Scr));
  XStoreName(Dpy, Win, PChar('Blaise + Xlib'));
  XSelectInput(Dpy, Win,
    ExposureMask or KeyPressMask or ButtonPressMask or StructureNotifyMask);

  { Ask the window manager to deliver close-button presses as a
    ClientMessage instead of killing the connection. }
  WmDelete := XInternAtom(Dpy, PChar('WM_DELETE_WINDOW'), 0);
  XSetWMProtocols(Dpy, Win, @WmDelete, 1);

  Gfx := XCreateGC(Dpy, Win, 0, nil);
  XMapWindow(Dpy, Win);

  Running := True;
  Exposed := False;
  Clicks := 0;
  while Running do
  begin
    XNextEvent(Dpy, @Ev);
    if XEvent_type_(Ev)^ = Expose then
    begin
      { Last expose in a batch has count = 0 — redraw once. }
      if XEvent_xexpose(Ev)^.count = 0 then
      begin
        DrawContents();
        if AutoClose and not Exposed then
        begin
          WriteLn('x11_window: exposed, sending self-close');
          SendSelfClose();
        end;
        Exposed := True;
      end;
    end
    else if XEvent_type_(Ev)^ = KeyPress then
    begin
      Key := XLookupKeysym(XEvent_xkey(Ev), 0);
      { XLookupKeysym with index 0 returns the UNSHIFTED keysym, so a
        letter key always reports its lowercase form — XK_q_ (the C
        XK_q; renamed by bindgen because Pascal folds case with XK_Q). }
      if (Key = XK_Escape) or (Key = XK_q_) then
        Running := False;
    end
    else if XEvent_type_(Ev)^ = ButtonPress then
    begin
      Clicks := Clicks + 1;
      Msg := 'click ' + IntToStr(Clicks) + ' at ' +
        IntToStr(XEvent_xbutton(Ev)^.x) + ',' +
        IntToStr(XEvent_xbutton(Ev)^.y);
      WriteLn('x11_window: ' + Msg);
      XDrawString(Dpy, Win, Gfx, XEvent_xbutton(Ev)^.x,
        XEvent_xbutton(Ev)^.y, PChar(Msg), Length(Msg));
    end
    else if XEvent_type_(Ev)^ = ClientMessage then
    begin
      if UInt64(XEvent_xclient(Ev)^.data.raw[0]) = UInt64(WmDelete) then
      begin
        WriteLn('x11_window: WM_DELETE_WINDOW received, quitting');
        Running := False;
      end;
    end;
  end;

  XFreeGC(Dpy, Gfx);
  XDestroyWindow(Dpy, Win);
  XCloseDisplay(Dpy);
  WriteLn('x11_window: clean shutdown');
end.
