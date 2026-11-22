import LeanTodomvc.App
import LeanTodomvc.Proof.Exec
import Mathlib.Data.List.Forall2

/-!
# The abstract model of the app, and how it is represented

`Model` is what the app's JS state boils down to. `Rep m s` says that the
browser state `s` represents `m`: the JS globals are determined by `m`, and
the visible document is exactly what `render()` produces from `m`, except for
the contents of input fields, which the user may have edited.
-/

namespace TodoMVC.Proof
open JS DOM

structure TodoR where
  id : Int
  title : String
  completed : Bool
  deriving DecidableEq, Repr

def TodoR.val (t : TodoR) : Value :=
  .obj [("id", .num t.id), ("title", .str t.title), ("completed", .bool t.completed)]

def todosVal (ts : List TodoR) : Value := .arr (ts.map TodoR.val)

structure Model where
  todos : List TodoR
  nextId : Int
  editingId : Int
  hash : String

def filterStr (h : String) : String :=
  if h = "#/active" then "active" else if h = "#/completed" then "completed" else "all"

def shows (f : String) (t : TodoR) : Bool :=
  if f = "active" then !t.completed else if f = "completed" then t.completed else true

def Model.shown (m : Model) : List TodoR := m.todos.filter (shows (filterStr m.hash))

def Model.activeCount (m : Model) : Nat := (m.todos.filter (!·.completed)).length

def Model.allDone (m : Model) : Bool := !m.todos.isEmpty && m.todos.all (·.completed)

/-- Model invariants: ids are distinct, non-negative, and below `nextId`. -/
structure Model.WF (m : Model) : Prop where
  nodup : (m.todos.map (·.id)).Nodup
  nonneg : ∀ t ∈ m.todos, 0 ≤ t.id
  lt : ∀ t ∈ m.todos, t.id < m.nextId

/-- Node indices of the static elements the script refers to. -/
abbrev nNewTodo : Nat := 5
abbrev nMain : Nat := 6
abbrev nToggleAll : Nat := 7
abbrev nList : Nat := 10
abbrev nFooter : Nat := 11
abbrev nCount : Nat := 12
abbrev nFilterAll : Nat := 15
abbrev nFilterActive : Nat := 18
abbrev nFilterCompleted : Nat := 21
abbrev nClear : Nat := 23

def globalsOf (m : Model) : List (String × Value) :=
  [("todos", todosVal m.todos), ("nextId", .num m.nextId), ("editingId", .num m.editingId),
   ("filter", .str (filterStr m.hash)),
   ("newTodo", .node nNewTodo), ("main", .node nMain), ("toggleAll", .node nToggleAll),
   ("list", .node nList), ("footer", .node nFooter), ("count", .node nCount),
   ("clearButton", .node nClear), ("filterAll", .node nFilterAll),
   ("filterActive", .node nFilterActive), ("filterCompleted", .node nFilterCompleted)]

def selectedIf (b : Bool) : String := if b then "selected" else ""

/-- The dynamic parts of the static nodes. -/
structure Dyn where
  /-- value of the new-todo field (edited by the user) -/
  v5 : String
  /-- value of the toggle-all checkbox (edited by the user) -/
  v7 : String
  mainHidden : Bool
  footerHidden : Bool
  toggleChecked : Bool
  clearHidden : Bool
  clsAll : String
  clsActive : String
  clsCompleted : String
  lis : List Nat
  cnt : List Nat

/-- The static nodes `0 … 24`, given their dynamic parts. -/
def staticNodeD (d : Dyn) : Nat → Node
  | 0 => { tag := "body", children := [1] }
  | 1 => { tag := "section", className := "todoapp", children := [2, 6, 11], parent := some 0 }
  | 2 => { tag := "header", className := "header", children := [3, 5], parent := some 1 }
  | 3 => { tag := "h1", children := [4], parent := some 2 }
  | 4 => { tag := "#text", text := "todos", parent := some 3 }
  | 5 => { tag := "input", className := "new-todo",
           attrs := [("placeholder", "What needs to be done?"), ("autofocus", "")],
           value := d.v5, parent := some 2, listeners := [("keydown", .fn "onNewTodoKey" [])] }
  | 6 => { tag := "section", className := "main", hidden := d.mainHidden,
           children := [7, 8, 10], parent := some 1 }
  | 7 => { tag := "input", id := "toggle-all", className := "toggle-all", attrs := [("type", "checkbox")],
           value := d.v7, checked := d.toggleChecked, parent := some 6,
           listeners := [("click", .fn "onToggleAll" [])] }
  | 8 => { tag := "label", attrs := [("for", "toggle-all")], children := [9], parent := some 6 }
  | 9 => { tag := "#text", text := "Mark all as complete", parent := some 8 }
  | 10 => { tag := "ul", className := "todo-list", children := d.lis, parent := some 6 }
  | 11 => { tag := "footer", className := "footer", hidden := d.footerHidden,
            children := [12, 13, 23], parent := some 1 }
  | 12 => { tag := "span", className := "todo-count", children := d.cnt, parent := some 11 }
  | 13 => { tag := "ul", className := "filters", children := [14, 17, 20], parent := some 11 }
  | 14 => { tag := "li", children := [15], parent := some 13 }
  | 15 => { tag := "a", id := "filter-all", className := d.clsAll,
            attrs := [("href", "#/")], children := [16], parent := some 14 }
  | 16 => { tag := "#text", text := "All", parent := some 15 }
  | 17 => { tag := "li", children := [18], parent := some 13 }
  | 18 => { tag := "a", id := "filter-active", className := d.clsActive,
            attrs := [("href", "#/active")], children := [19], parent := some 17 }
  | 19 => { tag := "#text", text := "Active", parent := some 18 }
  | 20 => { tag := "li", children := [21], parent := some 13 }
  | 21 => { tag := "a", id := "filter-completed", className := d.clsCompleted,
            attrs := [("href", "#/completed")], children := [22], parent := some 20 }
  | 22 => { tag := "#text", text := "Completed", parent := some 21 }
  | 23 => { tag := "button", className := "clear-completed", hidden := d.clearHidden,
            children := [24], parent := some 11, listeners := [("click", .fn "clearCompleted" [])] }
  | 24 => { tag := "#text", text := "Clear completed", parent := some 23 }
  | _ => default

/-- The dynamic parts as they should be for the model `m`. -/
def Model.dyn (m : Model) (v5 v7 : String) (lis cnt : List Nat) : Dyn where
  v5 := v5
  v7 := v7
  mainHidden := m.todos.isEmpty
  footerHidden := m.todos.isEmpty
  toggleChecked := m.allDone
  clearHidden := !m.todos.any (·.completed)
  clsAll := selectedIf (filterStr m.hash = "all")
  clsActive := selectedIf (filterStr m.hash = "active")
  clsCompleted := selectedIf (filterStr m.hash = "completed")
  lis := lis
  cnt := cnt

/-- The static nodes for the model `m`. -/
def staticNode (m : Model) (v5 v7 : String) (lis cnt : List Nat) : Nat → Node :=
  staticNodeD (m.dyn v5 v7 lis cnt)

/-! ## Rendered todo items

`renderTodo(t)` allocates a block of consecutive nodes starting at `b`:
`li`, `div.view`, `input.toggle`, `label`, the label's text (if the title is
non-empty), `button.destroy`, and, while editing, `input.edit`. -/

def liClass (t : TodoR) (ed : Bool) : String :=
  (if t.completed then "completed" else "") ++ (if ed then " editing" else "")

/-- Offset of the destroy button (after the label's optional text node). -/
def dOff (t : TodoR) : Nat := if t.title = "" then 4 else 5

/-- The size of a block. -/
def blockSize (t : TodoR) (ed : Bool) : Nat := dOff t + 1 + (if ed then 1 else 0)

/-- The block of nodes for `t` at `b`, attached to `parent`. `v2` and `ve` are the
values of the checkbox and the edit field. -/
def blockNode (b : Nat) (t : TodoR) (ed : Bool) (parent : Option Nat) (v2 ve : String) :
    Nat → Node
  | 0 => { tag := "li", className := liClass t ed,
           children := [b + 1] ++ (if ed then [b + dOff t + 1] else []), parent }
  | 1 => { tag := "div", className := "view", hidden := ed,
           children := [b + 2, b + 3, b + dOff t], parent := some b }
  | 2 => { tag := "input", className := "toggle", attrs := [("type", "checkbox")], value := v2,
           checked := t.completed, parent := some (b + 1),
           listeners := [("click", .fn "toggleTodo" [.num t.id])] }
  | 3 => { tag := "label", children := (if t.title = "" then [] else [b + 4]), parent := some (b + 1),
           listeners := [("dblclick", .fn "startEditing" [.num t.id])] }
  | i =>
    if t.title ≠ "" ∧ i = 4 then { tag := "#text", text := t.title, parent := some (b + 3) }
    else if i = dOff t then
      { tag := "button", className := "destroy", parent := some (b + 1),
        listeners := [("click", .fn "destroyTodo" [.num t.id])] }
    else if ed ∧ i = dOff t + 1 then
      { tag := "input", className := "edit", value := ve, parent := some b,
        listeners := [("keydown", .fn "onEditKey" [.num t.id]), ("blur", .fn "onEditBlur" [.num t.id])] }
    else default

/-- Allocate the nodes `f 0, …, f (n - 1)`. -/
def allocMany (w : World) (f : Nat → Node) : Nat → World
  | 0 => w
  | n + 1 => ((allocMany w f n).alloc (f n)).1

/-- The world after `renderTodo(t)`: a fresh, unattached block. -/
def renderTodoW (w : World) (t : TodoR) (ed : Bool) : World :=
  allocMany w (blockNode w.dom.size t ed none "" t.title) (blockSize t ed)

/-- `w` contains the block for `t` at `b`, attached to `parent`. -/
def Block (w : World) (b : Nat) (t : TodoR) (ed : Bool) (parent : Option Nat) : Prop :=
  b + blockSize t ed ≤ w.dom.size ∧
  ∃ v2 ve, ∀ i < blockSize t ed, w.node (b + i) = blockNode b t ed parent v2 ve i

/-! ## The counter: `<strong>n</strong>` followed by " item(s) left" -/

def countLabel (n : Nat) : String := if n = 1 then " item left" else " items left"

/-- `w` contains the counter nodes at `c` (strong, its text, the label). -/
def Counter (w : World) (c : Nat) (n : Nat) : Prop :=
  c + 3 ≤ w.dom.size ∧
  w.node c = { tag := "strong", children := [c + 1], parent := some nCount } ∧
  w.node (c + 1) = { tag := "#text", text := toString n, parent := some c } ∧
  w.node (c + 2) = { tag := "#text", text := countLabel n, parent := some nCount }

/-! ## Well-formedness of the DOM -/

/-- The document of `w` represents `m`. -/
structure DomRep (m : Model) (w : World) : Prop where
  size : 25 ≤ w.dom.size
  static : ∃ v5 v7 lis c, (∀ k < 25, w.node k = staticNode m v5 v7 lis [c, c + 2] k) ∧
    List.Forall₂ (fun b t => Block w b t (m.editingId = t.id) (some nList)) lis m.shown ∧
    Counter w c m.activeCount
  wf : World.ParentWF w
  lt : World.ParentLt w

def storageRep (m : Model) (st : List (String × String)) : Prop :=
  (st = [] ∧ m.todos = []) ∨ st = [(STORAGE_KEY, Json.stringify (todosVal m.todos))]

/-- The browser state `s` represents the model `m`. -/
structure Rep (m : Model) (s : State) : Prop where
  errors : s.errors = []
  funcs : s.world.funcs = funcs
  globals : s.world.globals = globalsOf m
  hash : s.world.hash = m.hash
  windowListeners : s.world.windowListeners = [("hashchange", .fn "route" [])]
  storage : storageRep m s.world.storage
  model : m.WF
  dom : DomRep m s.world

end TodoMVC.Proof
