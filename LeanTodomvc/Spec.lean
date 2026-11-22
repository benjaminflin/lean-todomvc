import LeanTodomvc.App
import LeanTodomvc.Mu

/-!
# The TodoMVC specification

The clauses of <https://github.com/tastejs/todomvc/blob/master/app-spec.md> as
modal μ-calculus formulas over the transition system `TodoMVC.app.step`, whose
atomic propositions are predicates on the state.

All predicates are about what the *user* can observe, namely the visible DOM
and `localStorage`, and never about the app's JS variables.
-/

namespace TodoMVC
open JS DOM Mu

abbrev Φ := Formula State Action

/-- The initial state: a fresh page with empty `localStorage`. -/
def s₀ : State := app.init

def Sat (φ : Φ) : Prop := Mu.Sat app.step s₀ φ

/-! ## Observations -/

/-- A todo as it is persisted, or as it is shown. -/
structure Todo where
  title : String
  completed : Bool
  deriving DecidableEq, Repr

def parseTodo : Value → Option Todo
  | .obj fs =>
    match assocGet fs "title", assocGet fs "completed" with
    | some (.str t), some (.bool c) => some ⟨t, c⟩
    | _, _ => none
  | _ => none

/-- The todos in `localStorage` (none stored = no todos); `none` if malformed. -/
def stored (s : State) : Option (List Todo) :=
  match assocGet s.world.storage STORAGE_KEY with
  | none => some []
  | some str =>
    match Json.parse str with
    | some (.arr vs) => vs.mapM parseTodo
    | _ => none

def q (s : State) (sel : String) : Option Nat := s.world.querySelector sel

def isVisible (s : State) (sel : String) : Bool :=
  match q s sel with
  | some n => s.world.visible n
  | none => false

def text (s : State) (sel : String) : String :=
  match q s sel with
  | some n => s.world.textContent n
  | none => ""

/-- The `<li>`s of the todo list. -/
def items (s : State) : List Nat :=
  match q s ".todo-list" with
  | some n => (s.world.node n).children
  | none => []

/-- The first node in the subtree of `n` with the given class or tag. -/
def find (s : State) (n : Nat) (p : Node → Bool) : Option Nat :=
  (s.world.subtree n).find? fun m => p (s.world.node m)

def itemTodo (s : State) (li : Nat) : Todo :=
  ⟨match find s li (·.tag == "label") with
    | some l => s.world.textContent l
    | none => "",
   (s.world.node li).hasClass "completed"⟩

/-- The todos shown in the list. -/
def displayed (s : State) : List Todo := (items s).map (itemTodo s)

inductive Filter | all | active | completed
  deriving DecidableEq

def filter (s : State) : Filter :=
  if s.world.hash == "#/active" then .active
  else if s.world.hash == "#/completed" then .completed
  else .all

def Filter.shows : Filter → Todo → Bool
  | .all, _ => true
  | .active, t => !t.completed
  | .completed, t => t.completed

def newTodoValue (s : State) : String :=
  match q s ".new-todo" with
  | some n => (s.world.node n).value
  | none => ""

def isChecked (s : State) (sel : String) : Bool :=
  match q s sel with
  | some n => (s.world.node n).checked
  | none => false

def isEditing (s : State) : Bool := (items s).any fun li => (s.world.node li).hasClass "editing"

/-! ## Invariants

These should hold in every reachable state. Each is a Boolean predicate so
it can be both checked by running it and used as an atom. -/

def noErrors (s : State) : Bool := s.errors.isEmpty

/-- The list shows exactly the persisted todos which pass the current filter. -/
def listMatchesStorage (s : State) : Bool :=
  match stored s with
  | some ts => displayed s == ts.filter (filter s).shows
  | none => false

/-- "When there are no todos, `#main` and `#footer` should be hidden." -/
def hiddenWhenEmpty (s : State) : Bool :=
  match stored s with
  | some ts => (ts.isEmpty == !isVisible s ".main") && (ts.isEmpty == !isVisible s ".footer")
  | none => false

/-- "Displays the number of active todos in a pluralized form." -/
def counterCorrect (s : State) : Bool :=
  match stored s with
  | some ts =>
    let n := (ts.filter (!·.completed)).length
    ts.isEmpty || text s ".todo-count" == toString n ++ (if n == 1 then " item left" else " items left")
  | none => false

/-- "Clear completed" is shown iff there are completed todos. -/
def clearButtonCorrect (s : State) : Bool :=
  match stored s with
  | some ts => isVisible s ".clear-completed" == ts.any (·.completed)
  | none => false

/-- The toggle-all checkbox is checked iff all todos are completed. -/
def toggleAllCorrect (s : State) : Bool :=
  match stored s with
  | some ts => isChecked s ".toggle-all" == (!ts.isEmpty && ts.all (·.completed))
  | none => false

/-- Exactly the filter link of the current route is `.selected`. -/
def filterLinkCorrect (s : State) : Bool :=
  let sel (id : String) := match q s ("#" ++ id) with
    | some n => (s.world.node n).hasClass "selected"
    | none => false
  sel "filter-all" == (filter s == .all) && sel "filter-active" == (filter s == .active) &&
    sel "filter-completed" == (filter s == .completed)

/-- At most one todo is being edited. -/
def atMostOneEditing (s : State) : Bool :=
  ((items s).filter fun li => (s.world.node li).hasClass "editing").length ≤ 1

def invariant (s : State) : Bool :=
  noErrors s && listMatchesStorage s && hiddenWhenEmpty s && counterCorrect s &&
    clearButtonCorrect s && toggleAllCorrect s && filterLinkCorrect s && atMostOneEditing s

/-! ## Actions the specification talks about -/

def on (sel : String) (mk : Nat → Action) : State → Action → Prop :=
  fun s a => ∃ n, q s sel = some n ∧ a = mk n

def enterNewTodo := on ".new-todo" (.keydown · "Enter")
def clickClearCompleted := on ".clear-completed" .click
def clickToggleAll := on ".toggle-all" .click

/-! ## The specification -/

def atom (p : State → Bool) : Φ := .atom fun s => p s = true

/-- `p → φ`, using negation of the atom `p`. -/
def implies (p : State → Prop) (φ : Φ) : Φ := .or (.atom fun s => ¬ p s) φ

/-- Every reachable state satisfies the invariants. -/
def specInvariant : Φ := (atom invariant).AG

/-- "New todo: … on Enter, the todo should be created and appended to the list;
the input should be cleared; `.trim()` the input and make sure it's not empty
before creating a new todo." -/
def specNewTodo (v : String) (ts : List Todo) : Φ :=
  .AG <| implies (fun s => newTodoValue s = v ∧ stored s = some ts) <|
    .box enterNewTodo <| .atom fun s =>
      if jsTrim v = "" then stored s = some ts
      else stored s = some (ts ++ [⟨jsTrim v, false⟩]) ∧ newTodoValue s = ""

/-- "Clear completed: removes completed todos when clicked." -/
def specClearCompleted (ts : List Todo) : Φ :=
  .AG <| implies (fun s => stored s = some ts) <|
    .box clickClearCompleted <| .atom fun s => stored s = some (ts.filter (!·.completed))

/-- "Mark all as complete: … mark all of the todos as complete [or, if they all
are, as active]." -/
def specToggleAll (ts : List Todo) : Φ :=
  .AG <| implies (fun s => stored s = some ts ∧ ts ≠ []) <|
    .box clickToggleAll <| .atom fun s =>
      stored s = some (ts.map fun t => { t with completed := !ts.all (·.completed) })

/-- "Persistence": reloading the page shows the same todos. -/
def specPersistence (ts : List Todo) : Φ :=
  .AG <| implies (fun s => stored s = some ts) <|
    .box (fun _ a => a = .reload) <| .atom fun s =>
      stored s = some ts ∧ displayed s = ts.filter (filter s).shows

/-- "Routing": following a filter link shows exactly the matching todos. -/
def specRouting : Φ :=
  .AG <| .box (on "#filter-active" .click) <| .atom fun s =>
    filter s = .active ∧ displayed s = ((stored s).getD []).filter (!·.completed)

/-- Liveness sanity check: it is possible to have a completed todo. -/
def specCanComplete : Φ :=
  .EF <| .atom fun s => ∃ t ∈ (stored s).getD [], t.completed

/-! ## Results -/

/-- A user session, as a list of actions computed from the current state. -/
def run (s : State) (as : List (State → Action)) : State :=
  as.foldl (fun s a => app.step s (a s)) s

def node (s : State) (sel : String) : Nat := (q s sel).getD 0

theorem run_reachable (as : List (State → Action)) :
    ∀ s, Reachable app.step s (run s as) := by
  induction as with
  | nil => intro s; exact .refl
  | cons a as ih => intro s; exact .head ⟨a s, rfl⟩ (ih _)

theorem run_append (s : State) (as bs : List (State → Action)) :
    run s (as ++ bs) = run (run s as) bs := by
  simp [run, List.foldl_append]

theorem s₀_invariant : invariant s₀ = true := by native_decide

theorem canComplete : Sat specCanComplete := by
  refine (mem_EF _ _ _ _).2 ⟨run s₀ [
      fun s => .input (node s ".new-todo") "Write a spec",
      fun s => .keydown (node s ".new-todo") "Enter",
      fun s => .click (node s ".toggle")], run_reachable _ _, ?_⟩
  · refine ⟨⟨"Write a spec", true⟩, ?_, rfl⟩
    have : (stored (run s₀ [
      fun s => .input (node s ".new-todo") "Write a spec",
      fun s => .keydown (node s ".new-todo") "Enter",
      fun s => .click (node s ".toggle")])).getD [] = [⟨"Write a spec", true⟩] := by native_decide
    rw [this]; simp

/-! ### Bounded checking of the invariants

Exhaustive search over all paths of a few steps, from a number of reachable
seed states. The actions are every interaction with every visible control
(with a few representative strings typed into text fields), plus
navigation and reload. -/

def actions (s : State) : List Action :=
  let w := s.world
  (w.documentNodes.filter w.visible).flatMap (fun n =>
    let nd := w.node n
    match nd.tag with
    | "input" =>
      if nd.attr "type" == some "checkbox" then [.click n]
      else [.input n "a", .input n " b ", .input n " ", .keydown n "Enter", .keydown n "Escape", .blur n]
    | "label" => [.click n, .dblclick n]
    | "button" | "a" => [.click n]
    | _ => []) ++
  [.navigate "#/completed", .reload]

def add (title : String) : List (State → Action) :=
  [fun s => .input (node s ".new-todo") title, fun s => .keydown (node s ".new-todo") "Enter"]

def firstLabel (s : State) : Nat := (find s (node s ".todo-list") (·.tag == "label")).getD 0

/-- Reachable seed states: empty; two todos with one completed; the same
filtered to active; and while editing. -/
def seeds : List State :=
  let two := run s₀ (add "a" ++ add "b" ++ [fun s => .click (node s ".toggle")])
  [s₀, two, run two [fun _ => .navigate "#/active"], run two [fun s => .dblclick (firstLabel s)]]

theorem seeds_reachable : ∀ s ∈ seeds, Reachable app.step s₀ s := by
  simp only [seeds, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl)
  · exact .refl
  · exact run_reachable _ _
  · rw [← run_append]; exact run_reachable _ _
  · rw [← run_append]; exact run_reachable _ _

theorem bounded_invariant :
    ∀ s ∈ seeds, s ∈ sem app.step ((atom invariant).AGn (fun s a => a ∈ actions s) 3) (fun _ => ∅) := by
  intro s hs
  apply checkAGn_sound
  revert s
  native_decide

/-! ## Open obligations

These are the full, unbounded statements. Proving them needs inductive
invariants for the app, and reasoning about the interpreter on *symbolic*
states. This is not done yet. -/

theorem invariant_holds : Sat specInvariant := by sorry

end TodoMVC
