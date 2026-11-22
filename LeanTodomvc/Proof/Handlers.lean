import LeanTodomvc.Proof.RenderRep

/-!
# The event handlers
-/

namespace TodoMVC.Proof
open JS DOM
open World (ParentWF ParentLt Chain)

/-- What the handlers need to know about the world. -/
structure Pre (m : Model) (w : World) : Prop where
  render : RenderPre m w
  wf : ParentWF w
  static : ∃ d, ∀ k < 25, w.node k = staticNodeD d k
  count : ∀ c ∈ (w.node nCount).children, 25 ≤ c ∧ c < w.dom.size

/-- The world `w` with new globals and storage. -/
abbrev withState (w : World) (g : List (String × Value)) (st : List (String × String)) : World :=
  (w.setGlobals g).setStorage st

theorem pre_withState {m m' : Model} {w : World} (h : Pre m w) (st : List (String × String)) :
    Pre m' (withState w (globalsOf m') st) where
  render := {
    funcs := h.render.funcs, globals := rfl, size := h.render.size,
    listChain := by simpa using h.render.listChain, lt := by simpa using h.render.lt,
    listChildren := h.render.listChildren }
  wf := by simpa using h.wf
  static := h.static
  count := h.count

/-- `render()`, in a form `simp` can use: the model is given explicitly and the
preconditions are separate facts. -/
theorem spec_render' (m : Model) {l : Locals} {w : World} (hf : w.funcs = TodoMVC.funcs)
    (hg : w.globals = globalsOf m) (hs : 25 ≤ w.dom.size) (hc : Chain w nList listChain) (hl : ParentLt w)
    (hch : ∀ c ∈ (w.node nList).children, 25 ≤ c) :
    R (callValue (.fn "render" []) []) l w = some (.ok ((.undef, l), renderW m w)) :=
  spec_render ⟨hf, hg, hs, hc, hl, hch⟩

theorem spec_save (m : Model) {l : Locals} {w : World} (hf : w.funcs = TodoMVC.funcs)
    (hg : w.globals = globalsOf m) :
    R (callValue (.fn "save" []) []) l w =
      some (.ok ((.undef, l), w.setStorage (assocSet w.storage STORAGE_KEY (Json.stringify (todosVal m.todos))))) := by
  rw [callFn lk_save hf]
  js_simp [Fn.save, hg, globalsOf, STORAGE_KEY]

/-- Save the model's todos. -/
def saveStorage (m : Model) (st : List (String × String)) : List (String × String) :=
  assocSet st STORAGE_KEY (Json.stringify (todosVal m.todos))

def Model.toggle (m : Model) (id : Int) : Model :=
  { m with todos := m.todos.map fun t => if t.id = id then { t with completed := !t.completed } else t }

theorem spec_toggleTodo {m : Model} {l : Locals} {w : World} (h : Pre m w) (id : Int) (ev : Value) :
    R (callValue (.fn "toggleTodo" [.num id]) [ev]) l w =
      some (.ok ((.undef, l), renderW (m.toggle id)
        (withState w (globalsOf (m.toggle id)) (saveStorage (m.toggle id) w.storage)))) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_toggleTodo hf]
  have hmap := spec_mapArr (g := .fn "flipIfId" [.num id])
    (f := fun t => if t.id = id then { t with completed := !t.completed } else t) (w := w) m.todos
    (fun t _ l => spec_flipIfId hf id t)
  js_simp [Fn.toggleTodo, hf, hg, globalsOf, todosVal, hmap, TodoMVC.funcs]
  rw [spec_save (m.toggle id) (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.toggle])]
  js_simp [hf, TodoMVC.funcs]
  rw [spec_render' (m.toggle id) (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.toggle])
    (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
    (by simpa using h.render.listChildren)]
  js_simp [withState, saveStorage, Model.toggle, todosVal, globalsOf]

def Model.destroy (m : Model) (id : Int) : Model :=
  { m with todos := m.todos.filter fun t => decide (t.id ≠ id) }

theorem spec_destroyTodo {m : Model} {l : Locals} {w : World} (h : Pre m w) (id : Int) (ev : Value) :
    R (callValue (.fn "destroyTodo" [.num id]) [ev]) l w =
      some (.ok ((.undef, l), renderW (m.destroy id)
        (withState w (globalsOf (m.destroy id)) (saveStorage (m.destroy id) w.storage)))) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_destroyTodo hf]
  have hfil := spec_filterArr (g := .fn "hasOtherId" [.num id]) (p := fun t => decide (t.id ≠ id)) (w := w)
    m.todos (fun t _ l => spec_hasOtherId hf id t)
  js_simp [Fn.destroyTodo, hf, hg, globalsOf, todosVal, hfil, TodoMVC.funcs]
  rw [spec_save (m.destroy id) (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.destroy])]
  js_simp [hf, TodoMVC.funcs]
  rw [spec_render' (m.destroy id) (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.destroy])
    (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
    (by simpa using h.render.listChildren)]
  js_simp [withState, saveStorage, Model.destroy, todosVal, globalsOf]

def Model.clear (m : Model) : Model := { m with todos := m.todos.filter fun t => !t.completed }

theorem spec_clearCompleted {m : Model} {l : Locals} {w : World} (h : Pre m w) (ev : Value) :
    R (callValue (.fn "clearCompleted" []) [ev]) l w =
      some (.ok ((.undef, l), renderW m.clear
        (withState w (globalsOf m.clear) (saveStorage m.clear w.storage)))) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_clearCompleted hf]
  have hfil := spec_filterArr (g := .fn "isActive" []) (p := fun t => !t.completed) (w := w)
    m.todos (fun t _ l => spec_isActive hf t)
  js_simp [Fn.clearCompleted, hf, hg, globalsOf, todosVal, hfil, TodoMVC.funcs]
  rw [spec_save m.clear (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.clear])]
  js_simp [hf, TodoMVC.funcs]
  rw [spec_render' m.clear (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.clear])
    (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
    (by simpa using h.render.listChildren)]
  js_simp [withState, saveStorage, Model.clear, todosVal, globalsOf]

def Model.setAll (m : Model) (c : Bool) : Model :=
  { m with todos := m.todos.map fun t => { t with completed := c } }

theorem spec_onToggleAll {m : Model} {l : Locals} {w : World} (h : Pre m w) (ev : Value) :
    R (callValue (.fn "onToggleAll" []) [ev]) l w =
      some (.ok ((.undef, l), renderW (m.setAll (w.node nToggleAll).checked)
        (withState w (globalsOf (m.setAll (w.node nToggleAll).checked))
          (saveStorage (m.setAll (w.node nToggleAll).checked) w.storage)))) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_onToggleAll hf]
  have hmap := spec_mapArr (g := .fn "setCompletedTo" [.bool (w.node nToggleAll).checked])
    (f := fun t => { t with completed := (w.node nToggleAll).checked })
    (w := w) m.todos (fun t _ l => spec_setCompletedTo hf _ t)
  js_simp [Fn.onToggleAll, hf, hg, globalsOf, todosVal, hmap, TodoMVC.funcs]
  rw [spec_save (m.setAll (w.node nToggleAll).checked) (by simp [hf])
    (by js_simp [globalsOf, todosVal, Model.setAll])]
  js_simp [hf, TodoMVC.funcs]
  rw [spec_render' (m.setAll (w.node nToggleAll).checked) (by simp [hf])
    (by js_simp [globalsOf, todosVal, Model.setAll])
    (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
    (by simpa using h.render.listChildren)]
  js_simp [withState, saveStorage, Model.setAll, todosVal, globalsOf]

def Model.startEdit (m : Model) (id : Int) : Model := { m with editingId := id }

theorem spec_startEditing {m : Model} {l : Locals} {w : World} (h : Pre m w) (id : Int) (ev : Value) :
    R (callValue (.fn "startEditing" [.num id]) [ev]) l w =
      some (.ok ((.undef, l), renderW (m.startEdit id) (w.setGlobals (globalsOf (m.startEdit id))))) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_startEditing hf]
  js_simp [Fn.startEditing, hf, hg, globalsOf, TodoMVC.funcs]
  rw [spec_render' (m.startEdit id) (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.startEdit])
    (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
    (by simpa using h.render.listChildren)]
  js_simp [Model.startEdit, todosVal, globalsOf]

def Model.route (m : Model) (h : String) : Model := { m with hash := h }

theorem spec_route {m : Model} {l : Locals} {w : World} (h : Pre m w) (args : List Value) :
    R (callValue (.fn "route" []) args) l w =
      some (.ok ((.undef, l), renderW (m.route w.hash) (w.setGlobals (globalsOf (m.route w.hash))))) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_route hf]
  by_cases h1 : w.hash = "#/active"
  · js_simp [Fn.route, hf, hg, h1, globalsOf, TodoMVC.funcs]
    rw [spec_render' (m.route "#/active") (by simp [hf]) (by js_simp [globalsOf, Model.route, filterStr])
      (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
      (by simpa using h.render.listChildren)]
    js_simp [globalsOf, Model.route, filterStr]
  by_cases h2 : w.hash = "#/completed"
  · js_simp [Fn.route, hf, hg, h1, h2, globalsOf, TodoMVC.funcs]
    rw [spec_render' (m.route "#/completed") (by simp [hf]) (by js_simp [globalsOf, Model.route, filterStr])
      (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
      (by simpa using h.render.listChildren)]
    js_simp [globalsOf, Model.route, filterStr]
  · js_simp [Fn.route, hf, hg, h1, h2, globalsOf, TodoMVC.funcs]
    rw [spec_render' (m.route w.hash) (by simp [hf]) (by js_simp [globalsOf, Model.route, filterStr, h1, h2])
      (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
      (by simpa using h.render.listChildren)]
    js_simp [globalsOf, Model.route, filterStr, h1, h2]

def Model.add (m : Model) (title : String) : Model :=
  { m with todos := m.todos ++ [⟨m.nextId, title, false⟩], nextId := m.nextId + 1 }

theorem spec_onNewTodoKey {m : Model} {l : Locals} {w : World} (h : Pre m w) (n : Nat) (key : String) :
    R (callValue (.fn "onNewTodoKey" []) [State.eventObj "keydown" n key]) l w =
      some (.ok ((.undef, l),
        if key = "Enter" ∧ jsTrim (w.node nNewTodo).value ≠ "" then
          renderW (m.add (jsTrim (w.node nNewTodo).value))
            (withState (w.modify nNewTodo fun nd => { nd with value := "" })
              (globalsOf (m.add (jsTrim (w.node nNewTodo).value)))
              (saveStorage (m.add (jsTrim (w.node nNewTodo).value)) w.storage))
        else w)) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_onNewTodoKey hf]
  by_cases hk : key = "Enter"
  swap
  · js_simp [Fn.onNewTodoKey, hf, hg, hk, globalsOf, TodoMVC.funcs, State.eventObj]
  by_cases ht : jsTrim (w.node nNewTodo).value = ""
  · js_simp [Fn.onNewTodoKey, hf, hg, hk, ht, globalsOf, TodoMVC.funcs, State.eventObj]
  js_simp [Fn.onNewTodoKey, hf, hg, hk, ht, globalsOf, todosVal, TodoMVC.funcs, State.eventObj]
  rw [spec_save (m.add (jsTrim (w.node nNewTodo).value)) (by simp [hf])
    (by js_simp [globalsOf, todosVal, Model.add, TodoR.val, List.map_append, List.map_cons, List.map_nil])]
  js_simp [hf, TodoMVC.funcs]
  rw [spec_render' (m.add (jsTrim (w.node nNewTodo).value)) (by simp [hf])
    (by js_simp [globalsOf, todosVal, Model.add, TodoR.val, List.map_append, List.map_cons, List.map_nil])
    (by simpa using h.render.size)
    (by simp only [World.chain_setStorage, World.chain_setGlobals]; refine (World.chain_modify_iff ?_ _ _).2 h.render.listChain; intro; rfl)
    (by simp only [World.parentLt_setStorage, World.parentLt_setGlobals]; refine World.parentLt_modify_of h.render.lt ?_; intro; rfl)
    (by simpa using h.render.listChildren)]
  js_simp [withState, saveStorage, Model.add, todosVal, globalsOf, TodoR.val, List.map_append, List.map_cons, List.map_nil]

def Model.setTitle (m : Model) (id : Int) (title : String) : Model :=
  { m with todos := m.todos.map fun t => if t.id = id then { t with title := title } else t }

/-- Leave editing mode, committing the trimmed `title` (deleting the todo if blank). -/
def Model.finish (m : Model) (id : Int) (title : String) : Model :=
  if title = "" then ({ m with editingId := -1 } : Model).destroy id
  else ({ m with editingId := -1 } : Model).setTitle id title

theorem spec_finishEditing {m : Model} {l : Locals} {w : World} (h : Pre m w) (id : Int)
    (type key : String) (n : Nat) :
    R (callValue (.fn "finishEditing" []) [.num id, State.eventObj type n key]) l w =
      some (.ok ((.undef, l),
        if m.editingId = id then
          renderW (m.finish id (jsTrim (w.node n).value))
            (withState w (globalsOf (m.finish id (jsTrim (w.node n).value)))
              (saveStorage (m.finish id (jsTrim (w.node n).value)) w.storage))
        else w)) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_finishEditing hf]
  by_cases he : m.editingId = id
  swap
  · js_simp [Fn.finishEditing, hf, hg, he, globalsOf, TodoMVC.funcs, State.eventObj]
  by_cases ht : jsTrim (w.node n).value = ""
  · have hfil := fun g => spec_filterArr (g := .fn "hasOtherId" [.num id]) (p := fun t => decide (t.id ≠ id))
      (w := w.setGlobals g) m.todos (fun t _ l => spec_hasOtherId (by simp [hf]) id t)
    js_simp [Fn.finishEditing, hf, hg, he, ht, globalsOf, todosVal, hfil, TodoMVC.funcs, State.eventObj]
    rw [spec_save (m.finish id "") (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.finish, Model.destroy])]
    js_simp [hf, TodoMVC.funcs]
    rw [spec_render' (m.finish id "") (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.finish, Model.destroy])
      (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
      (by simpa using h.render.listChildren)]
    js_simp [withState, saveStorage, Model.finish, Model.destroy, todosVal, globalsOf]
  · have hmap := fun g => spec_mapArr (g := .fn "setTitleIfId" [.num id, .str (jsTrim (w.node n).value)])
      (f := fun t => if t.id = id then { t with title := jsTrim (w.node n).value } else t)
      (w := w.setGlobals g) m.todos (fun t _ l => spec_setTitleIfId (by simp [hf]) id _ t)
    js_simp [Fn.finishEditing, hf, hg, he, ht, globalsOf, todosVal, hmap, TodoMVC.funcs, State.eventObj]
    rw [spec_save (m.finish id (jsTrim (w.node n).value)) (by simp [hf])
      (by js_simp [globalsOf, todosVal, Model.finish, Model.setTitle, ht])]
    js_simp [hf, TodoMVC.funcs]
    rw [spec_render' (m.finish id (jsTrim (w.node n).value)) (by simp [hf])
      (by js_simp [globalsOf, todosVal, Model.finish, Model.setTitle, ht])
      (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
      (by simpa using h.render.listChildren)]
    js_simp [withState, saveStorage, Model.finish, Model.setTitle, todosVal, globalsOf, ht]

def Model.cancelEdit (m : Model) : Model := { m with editingId := -1 }

theorem spec_onEditKey {m : Model} {l : Locals} {w : World} (h : Pre m w) (id : Int) (n : Nat) (key : String) :
    R (callValue (.fn "onEditKey" [.num id]) [State.eventObj "keydown" n key]) l w =
      some (.ok ((.undef, l),
        if key = "Enter" then
          if m.editingId = id then
            renderW (m.finish id (jsTrim (w.node n).value))
              (withState w (globalsOf (m.finish id (jsTrim (w.node n).value)))
                (saveStorage (m.finish id (jsTrim (w.node n).value)) w.storage))
          else w
        else if key = "Escape" then
          renderW m.cancelEdit (w.setGlobals (globalsOf m.cancelEdit))
        else w)) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_onEditKey hf]
  by_cases hk : key = "Enter"
  · subst hk
    js_simp [Fn.onEditKey, hf, hg, globalsOf, TodoMVC.funcs, State.eventObj]
    rw [show Value.obj _ = State.eventObj "keydown" n "Enter" from rfl, spec_finishEditing h]
    rfl
  by_cases hk' : key = "Escape"
  · subst hk'
    js_simp [Fn.onEditKey, hf, hg, globalsOf, TodoMVC.funcs, State.eventObj]
    rw [spec_render' m.cancelEdit (by simp [hf]) (by js_simp [globalsOf, todosVal, Model.cancelEdit])
      (by simpa using h.render.size) (by simpa using h.render.listChain) (by simpa using h.render.lt)
      (by simpa using h.render.listChildren)]
    js_simp [Model.cancelEdit, todosVal, globalsOf]
  · js_simp [Fn.onEditKey, hf, hg, hk, hk', globalsOf, TodoMVC.funcs, State.eventObj]

theorem spec_onEditBlur {m : Model} {l : Locals} {w : World} (h : Pre m w) (id : Int) (n : Nat) :
    R (callValue (.fn "onEditBlur" [.num id]) [State.eventObj "blur" n]) l w =
      some (.ok ((.undef, l),
        if m.editingId = id then
          renderW (m.finish id (jsTrim (w.node n).value))
            (withState w (globalsOf (m.finish id (jsTrim (w.node n).value)))
              (saveStorage (m.finish id (jsTrim (w.node n).value)) w.storage))
        else w)) := by
  have hf := h.render.funcs
  have hg := h.render.globals
  rw [callFn lk_onEditBlur hf]
  js_simp [Fn.onEditBlur, hf, hg, globalsOf, TodoMVC.funcs]
  rw [spec_finishEditing h]
  rfl

end TodoMVC.Proof
