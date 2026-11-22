import LeanTodomvc.JS.Json

/-!
# A model of the DOM

The DOM is an *arena* of nodes indexed by `Nat`; node `0` is the document root
(`<body>`). Nodes are never freed: removing a node just detaches it, and
detached nodes are invisible and receive no user events.

We do not model CSS. Visibility is controlled by the `hidden` attribute only,
so the app sets `hidden` explicitly where TodoMVC's stylesheet would hide
something.
-/

namespace DOM
open JS

structure Node where
  tag : String
  /-- the `id` attribute -/
  id : String := ""
  className : String := ""
  /-- other attributes (`type`, `href`, `for`, `placeholder`, …) -/
  attrs : List (String × String) := []
  /-- text content of a `#text` node -/
  text : String := ""
  value : String := ""
  checked : Bool := false
  hidden : Bool := false
  children : List Nat := []
  parent : Option Nat := none
  /-- event listeners, in registration order: event type and function value -/
  listeners : List (String × Value) := []
  deriving Repr, Inhabited

def Node.attr (n : Node) (k : String) : Option String := (n.attrs.find? (·.1 == k)).map (·.2)

/-- Split on spaces, dropping empty pieces. (Structural, so it can be evaluated
in proofs, unlike `String.splitOn`.) -/
def splitSpaces : List Char → List Char → List String
  | [], [] => []
  | [], cur => [String.ofList cur.reverse]
  | ' ' :: cs, [] => splitSpaces cs []
  | ' ' :: cs, cur => String.ofList cur.reverse :: splitSpaces cs []
  | c :: cs, cur => splitSpaces cs (c :: cur)

def Node.classes (n : Node) : List String := splitSpaces n.className.toList []

def Node.hasClass (n : Node) (c : String) : Bool := n.classes.contains c

/-- Simple static HTML markup. -/
inductive Html where
  | el (tag : String) (attrs : List (String × String)) (children : List Html)
  | text (s : String)
  deriving Repr, Inhabited

end DOM

/-- Everything the page knows about: DOM, JS globals, `localStorage`, URL. -/
structure World where
  dom : Array DOM.Node
  /-- global JS variables -/
  globals : List (String × JS.Value) := []
  /-- declared JS functions -/
  funcs : List (String × JS.FunDef) := []
  /-- `localStorage` -/
  storage : List (String × String) := []
  /-- `location.hash` -/
  hash : String := ""
  /-- listeners registered on `window` -/
  windowListeners : List (String × JS.Value) := []
  deriving Inhabited

namespace World
open DOM

/-! Setters for the non-DOM parts. (Named functions rather than structure
updates, so that proofs can treat them as opaque.) -/

def setGlobals (w : World) (g : List (String × JS.Value)) : World := { w with globals := g }
def setStorage (w : World) (st : List (String × String)) : World := { w with storage := st }
def setFuncs (w : World) (fs : List (String × JS.FunDef)) : World := { w with funcs := fs }
def setHash (w : World) (h : String) : World := { w with hash := h }
def setWindowListeners (w : World) (ls : List (String × JS.Value)) : World := { w with windowListeners := ls }

def node? (w : World) (n : Nat) : Option Node := w.dom[n]?

def node (w : World) (n : Nat) : Node := w.dom[n]?.getD default

def modify (w : World) (n : Nat) (f : Node → Node) : World :=
  { w with dom := w.dom.modify n f }

def alloc (w : World) (nd : Node) : World × Nat :=
  ({ w with dom := w.dom.push nd }, w.dom.size)

/-- The ancestors of `n` (including `n`), following parent pointers. -/
def ancestors (w : World) (n : Nat) : List Nat :=
  go w.dom.size n
where
  go : Nat → Nat → List Nat
    | 0, _ => []
    | f + 1, n => n :: match (w.node n).parent with
      | some p => go f p
      | none => []

/-- `n` is in the document (connected to the root, node `0`). -/
def attached (w : World) (n : Nat) : Bool :=
  n < w.dom.size && (w.ancestors n).getLast? == some 0

/-- `n` is in the document and neither it nor any ancestor is `hidden`. -/
def visible (w : World) (n : Nat) : Bool :=
  w.attached n && (w.ancestors n).all fun a => !(w.node a).hidden

/-- Detach `c` from its parent, if any. -/
def detach (w : World) (c : Nat) : World :=
  match (w.node c).parent with
  | none => w
  | some p =>
    let w := w.modify p fun nd => { nd with children := nd.children.filter (· != c) }
    w.modify c fun nd => { nd with parent := none }

def appendChild (w : World) (p c : Nat) : World :=
  let w := w.detach c
  let w := w.modify p fun nd => { nd with children := nd.children ++ [c] }
  w.modify c fun nd => { nd with parent := some p }

def replaceChildren (w : World) (p : Nat) : World :=
  let cs := (w.node p).children
  let w := cs.foldl (fun w c => w.modify c fun nd => { nd with parent := none }) w
  w.modify p fun nd => { nd with children := [] }

/-- Nodes of the subtree rooted at `n`, in document (pre-)order. -/
def subtree (w : World) (n : Nat) : List Nat :=
  go w.dom.size n
where
  go : Nat → Nat → List Nat
    | 0, _ => []
    | f + 1, n => n :: ((w.node n).children.flatMap (go f))

/-- All nodes in the document, in document order. -/
def documentNodes (w : World) : List Nat := w.subtree 0

def textContent (w : World) (n : Nat) : String :=
  String.join ((w.subtree n).map fun m => (w.node m).text)

def setTextContent (w : World) (n : Nat) (s : String) : World :=
  let w := w.replaceChildren n
  if s == "" then w else
  let (w, t) := w.alloc { tag := "#text", text := s }
  w.appendChild n t

/-- `document.querySelector` for the simple selectors `#id`, `.class` and `tag`. -/
def querySelector (w : World) (sel : String) : Option Nat :=
  match sel.toList with
  | '#' :: id => w.documentNodes.find? fun n => (w.node n).id == String.ofList id
  | '.' :: c => w.documentNodes.find? fun n => (w.node n).hasClass (String.ofList c)
  | [] => none
  | tag => w.documentNodes.find? fun n => (w.node n).tag == String.ofList tag

/-- Load static markup into a fresh arena (node `0` is the root `body`). -/
def ofHtml (body : List Html) : World :=
  let w : World := { dom := #[{ tag := "body" }] }
  body.foldl (fun w h => (load w 0 h)) w
where
  load (w : World) (p : Nat) : Html → World
    | .text s =>
      let (w, t) := w.alloc { tag := "#text", text := s }
      w.appendChild p t
    | .el tag attrs cs =>
      let get k := (attrs.find? (·.1 == k)).map (·.2)
      let nd : Node := {
        tag, id := (get "id").getD "", className := (get "class").getD "",
        attrs := attrs.filter fun (k, _) => k != "id" && k != "class" && k != "hidden" && k != "checked",
        hidden := (get "hidden").isSome, checked := (get "checked").isSome }
      let (w, n) := w.alloc nd
      let w := w.appendChild p n
      loadList w n cs
  loadList (w : World) (p : Nat) : List Html → World
    | [] => w
    | h :: hs => loadList (load w p h) p hs

end World
