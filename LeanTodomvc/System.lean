import LeanTodomvc.JS.Interp

/-!
# The transition system

A web app is static markup plus a script. Its transition system has:

* states: the `World` (DOM, JS globals, `localStorage`, URL hash) plus a log of
  uncaught errors;
* actions: user events on DOM nodes, editing the URL, and reloading the page;
* a total, deterministic transition function `δ : State → Action → State`.

Events on nodes that are not visible (detached, or hidden) have no effect,
because the user cannot interact with them. An uncaught exception (or
divergence) in a listener is logged, and the effects of that listener are
discarded. (A browser would keep the effects made before the throw. The
specification requires there to be no errors, so this difference only matters
for apps that fail the specification anyway.)
-/

open JS DOM

structure App where
  html : List Html
  script : List Stmt

structure State where
  world : World
  /-- uncaught errors, most recent first -/
  errors : List String := []

inductive Action where
  | click (n : NodeId)
  | dblclick (n : NodeId)
  /-- the user edits the text of an input field to `v` -/
  | input (n : NodeId) (v : String)
  /-- a key press in a focused element; we do not model focus otherwise -/
  | keydown (n : NodeId) (key : String)
  | blur (n : NodeId)
  /-- the user edits the URL fragment -/
  | navigate (hash : String)
  | reload
  deriving Repr, DecidableEq

namespace State

/-- Run a JS computation. Errors and divergence are logged and roll back. -/
def run (s : State) (m : M Unit) : State :=
  match m.run' s.world with
  | some (.ok (_, w)) => { s with world := w }
  | some (.error e) => { s with errors := e :: s.errors }
  | none => { s with errors := "diverged" :: s.errors }

def eventObj (type : String) (target : NodeId) (key : String := "") : Value :=
  .obj [("type", .str type), ("key", .str key), ("target", .node target)]

/-- Call the listeners for `type` registered on `n`. Each listener runs as a
separate task, so one failing does not prevent the others from running. -/
def fire (s : State) (n : NodeId) (type : String) (key : String := "") : State :=
  let ls := ((s.world.node n).listeners.filter (·.1 == type)).map (·.2)
  ls.foldl (fun s l => s.run (fireListeners [l] (eventObj type n key))) s

def setHash (s : State) (h : String) : State :=
  if h == s.world.hash then s else
  let s := { s with world := { s.world with hash := h } }
  let ls := (s.world.windowListeners.filter (·.1 == "hashchange")).map (·.2)
  ls.foldl (fun s l => s.run (fireListeners [l] (eventObj "hashchange" 0))) s

/-- A click on `n`, including the browser's default actions: toggling a
checkbox, and following a `#fragment` link. -/
def click (s : State) (n : NodeId) : State :=
  let nd := s.world.node n
  let s := if nd.tag == "input" && nd.attr "type" == some "checkbox" then
      { s with world := s.world.modify n fun nd => { nd with checked := !nd.checked } }
    else s
  let s := s.fire n "click"
  match nd.tag, nd.attr "href" with
  | "a", some h => if h.startsWith "#" then s.setHash h else s
  | _, _ => s

end State

namespace App

def init (app : App) (storage : List (String × String) := []) (hash : String := "") : State :=
  let w := World.ofHtml app.html
  State.run { world := { w with storage, hash } } (runScript app.script)

def step (app : App) (s : State) : Action → State
  | .reload => app.init s.world.storage s.world.hash
  | .navigate h => s.setHash h
  | a =>
    let n := match a with
      | .click n | .dblclick n | .input n _ | .keydown n _ | .blur n => n
      | _ => 0
    if !s.world.visible n then s else
    match a with
    | .click n =>
      let nd := s.world.node n
      -- clicking a `<label for=…>` clicks the labelled control
      match nd.tag, nd.attr "for" with
      | "label", some id =>
        match s.world.documentNodes.find? (fun m => (s.world.node m).id == id) with
        | some m => s.click m
        | none => s
      | _, _ => s.click n
    | .dblclick n => s.fire n "dblclick"
    | .input n v =>
      if (s.world.node n).tag != "input" then s else
      let s := { s with world := s.world.modify n fun nd => { nd with value := v } }
      s.fire n "input"
    | .keydown n k => s.fire n "keydown" k
    | .blur n => s.fire n "blur"
    | _ => s

end App
