import LeanTodomvc.Proof.Model

/-!
# Specifications of the app's JS functions

Each lemma says what calling a function does, in terms of the model. They are
proved by symbolic execution with `js_simp`.
-/

namespace TodoMVC.Proof
open JS DOM

theorem lk_load : assocGet funcs "load" = some Fn.load := rfl
theorem lk_save : assocGet funcs "save" = some Fn.save := rfl
theorem lk_isActive : assocGet funcs "isActive" = some Fn.isActive := rfl
theorem lk_isShown : assocGet funcs "isShown" = some Fn.isShown := rfl
theorem lk_flipIfId : assocGet funcs "flipIfId" = some Fn.flipIfId := rfl
theorem lk_setCompletedTo : assocGet funcs "setCompletedTo" = some Fn.setCompletedTo := rfl
theorem lk_setTitleIfId : assocGet funcs "setTitleIfId" = some Fn.setTitleIfId := rfl
theorem lk_hasOtherId : assocGet funcs "hasOtherId" = some Fn.hasOtherId := rfl
theorem lk_onNewTodoKey : assocGet funcs "onNewTodoKey" = some Fn.onNewTodoKey := rfl
theorem lk_toggleTodo : assocGet funcs "toggleTodo" = some Fn.toggleTodo := rfl
theorem lk_destroyTodo : assocGet funcs "destroyTodo" = some Fn.destroyTodo := rfl
theorem lk_onToggleAll : assocGet funcs "onToggleAll" = some Fn.onToggleAll := rfl
theorem lk_clearCompleted : assocGet funcs "clearCompleted" = some Fn.clearCompleted := rfl
theorem lk_startEditing : assocGet funcs "startEditing" = some Fn.startEditing := rfl
theorem lk_finishEditing : assocGet funcs "finishEditing" = some Fn.finishEditing := rfl
theorem lk_onEditKey : assocGet funcs "onEditKey" = some Fn.onEditKey := rfl
theorem lk_onEditBlur : assocGet funcs "onEditBlur" = some Fn.onEditBlur := rfl
theorem lk_route : assocGet funcs "route" = some Fn.route := rfl
theorem lk_renderTodo : assocGet funcs "renderTodo" = some Fn.renderTodo := rfl
theorem lk_render : assocGet funcs "render" = some Fn.render := rfl

/-- Call a function of the app. -/
theorem callFn {name : String} {fd : FunDef} (hlk : assocGet funcs name = some fd)
    {bound args : List Value} {l : Locals} {w : World} (hf : w.funcs = funcs) :
    R (callValue (.fn name bound) args) l w =
      (R (execB fd.body) (some (fd.params.zipIdx.map fun (p, i) => (p, (bound ++ args).getD i .undef))) w).andThen
        fun o _ w => match o with
          | .ret v => some (.ok ((v, l), w))
          | .normal => some (.ok ((.undef, l), w)) :=
  R_callValue_fn (by rw [hf]; exact hlk)

section
variable {l : Locals} {w : World} (hf : w.funcs = funcs)
include hf

theorem spec_isActive (t : TodoR) :
    R (callValue (.fn "isActive" []) [t.val]) l w = some (.ok ((.bool !t.completed, l), w)) := by
  rw [callFn lk_isActive hf]
  js_simp [Fn.isActive, TodoR.val]

theorem spec_hasOtherId (id : Int) (t : TodoR) :
    R (callValue (.fn "hasOtherId" [.num id]) [t.val]) l w = some (.ok ((.bool (decide (t.id ≠ id)), l), w)) := by
  rw [callFn lk_hasOtherId hf]
  by_cases h : t.id = id <;> js_simp [Fn.hasOtherId, TodoR.val, h]

theorem spec_flipIfId (id : Int) (t : TodoR) :
    R (callValue (.fn "flipIfId" [.num id]) [t.val]) l w =
      some (.ok (((if t.id = id then { t with completed := !t.completed } else t).val, l), w)) := by
  rw [callFn lk_flipIfId hf]
  by_cases h : t.id = id <;> js_simp [Fn.flipIfId, TodoR.val, h]

theorem spec_setCompletedTo (c : Bool) (t : TodoR) :
    R (callValue (.fn "setCompletedTo" [.bool c]) [t.val]) l w =
      some (.ok (({ t with completed := c }.val, l), w)) := by
  rw [callFn lk_setCompletedTo hf]
  js_simp [Fn.setCompletedTo, TodoR.val]

theorem spec_setTitleIfId (id : Int) (title : String) (t : TodoR) :
    R (callValue (.fn "setTitleIfId" [.num id, .str title]) [t.val]) l w =
      some (.ok (((if t.id = id then { t with title := title } else t).val, l), w)) := by
  rw [callFn lk_setTitleIfId hf]
  by_cases h : t.id = id <;> js_simp [Fn.setTitleIfId, TodoR.val, h]

end

/-! ## `map` and `filter` with a JS callback which does not touch the state -/

theorem spec_mapArr {g : Value} {f : TodoR → TodoR} {w : World} :
    ∀ (ts : List TodoR), (∀ t ∈ ts, ∀ l, R (callValue g [t.val]) l w = some (.ok (((f t).val, l), w))) →
      ∀ l, R (mapArr g (ts.map TodoR.val)) l w = some (.ok (((ts.map f).map TodoR.val, l), w)) := by
  intro ts
  induction ts with
  | nil => intro _ l; rw [List.map_nil, mapArr]; rfl
  | cons t ts ih =>
    intro hg l
    rw [List.map_cons, mapArr]
    simp only [R_bind, hg t (by simp), Res.andThen_ok,
      ih (fun t ht => hg t (by simp [ht])), R_pure, List.map_cons]

theorem spec_filterArr {g : Value} {p : TodoR → Bool} {w : World} :
    ∀ (ts : List TodoR), (∀ t ∈ ts, ∀ l, R (callValue g [t.val]) l w = some (.ok ((.bool (p t), l), w))) →
      ∀ l, R (filterArr g (ts.map TodoR.val)) l w = some (.ok (((ts.filter p).map TodoR.val, l), w)) := by
  intro ts
  induction ts with
  | nil => intro _ l; rw [List.map_nil, filterArr]; rfl
  | cons t ts ih =>
    intro hg l
    rw [List.map_cons, filterArr]
    simp only [R_bind, hg t (by simp), Res.andThen_ok,
      ih (fun t ht => hg t (by simp [ht])), R_pure, truthy]
    rcases hp : p t <;> simp [List.filter_cons, hp]

theorem spec_isShown {m : Model} {l : Locals} {w : World} (hf : w.funcs = funcs)
    (hg : w.globals = globalsOf m) (t : TodoR) :
    R (callValue (.fn "isShown" []) [t.val]) l w =
      some (.ok ((.bool (shows (filterStr m.hash) t), l), w)) := by
  rw [callFn lk_isShown hf]
  generalize hfs : filterStr m.hash = f
  by_cases h1 : f = "active"
  · subst h1; js_simp [Fn.isShown, TodoR.val, hg, globalsOf, hfs, shows]
  · by_cases h2 : f = "completed"
    · subst h2; js_simp [Fn.isShown, TodoR.val, hg, globalsOf, hfs, shows]
    · js_simp [Fn.isShown, TodoR.val, hg, globalsOf, hfs, shows, h1, h2]

set_option maxHeartbeats 4000000 in
theorem spec_renderTodo {m : Model} {l : Locals} {w : World} (hf : w.funcs = funcs)
    (hg : w.globals = globalsOf m) (hs : 0 < w.dom.size) (t : TodoR) :
    R (callValue (.fn "renderTodo" []) [t.val]) l w =
      some (.ok ((.node w.dom.size, l), renderTodoW w t (decide (m.editingId = t.id)))) := by
  rw [callFn lk_renderTodo hf]
  obtain ⟨id, title, c⟩ := t
  cases c <;> by_cases he : m.editingId = id <;> by_cases ht : title = "" <;>
  · js_simp [Fn.renderTodo, TodoR.val, hf, hg, globalsOf, funcs, he, ht, hs, renderTodoW, allocMany,
      blockSize, dOff, blockNode, liClass]

end TodoMVC.Proof
