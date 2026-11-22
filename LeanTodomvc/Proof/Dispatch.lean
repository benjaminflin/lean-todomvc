import LeanTodomvc.Proof.Classify

/-!
# Dispatching user actions
-/

namespace TodoMVC.Proof
open JS DOM
open World (ParentWF ParentLt Chain SameButDom)

theorem fire_nil {s : State} {n : Nat} {type key : String}
    (h : (s.world.node n).listeners.filter (·.1 == type) = []) : s.fire n type key = s := by
  simp [State.fire, h]

theorem fire_one {s : State} {n : Nat} {type key : String} {f : Value}
    (h : (s.world.node n).listeners.filter (·.1 == type) = [(type, f)]) :
    s.fire n type key = s.run (fireListeners [f] (State.eventObj type n key)) := by
  simp [State.fire, h]

theorem State.with_world {s : State} (hs : s.errors = []) (w : World) : { s with world := w } = { world := w } := by
  cases s; simp_all

/-- A handler that ends with `render()`: it ran on `s`, and rendered `m'` from a world `w` which
satisfies the precondition. -/
theorem rep_run_render {m m' : Model} {s : State} (hs : s.errors = []) {w : World} (hpre : Pre m w)
    (hh : w.hash = m'.hash) (hwl : w.windowListeners = [("hashchange", .fn "route" [])])
    (hwf : m'.WF) (st : List (String × String)) (hst : storageRep m' st) {f ev v : Value} {l : Locals}
    (hR : R (callValue f [ev]) none s.world = some (.ok ((v, l), renderW m' (withState w (globalsOf m') st)))) :
    Rep m' (s.run (fireListeners [f] ev)) := by
  rw [run_fire1 _ _ _ hR, State.with_world hs]
  exact rep_renderW hpre hwf st hst hh hwl

/-- A handler that does nothing. -/
theorem run_same {s : State} {f ev v : Value} {l : Locals}
    (hR : R (callValue f [ev]) none s.world = some (.ok ((v, l), s.world))) :
    s.run (fireListeners [f] ev) = s := by
  rw [run_fire1 _ _ _ hR]

theorem blockNode_cases (t : TodoR) (ed : Bool) (i : Nat) (hi : i < blockSize t ed) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ (t.title ≠ "" ∧ i = 4) ∨ i = dOff t ∨ (ed = true ∧ i = dOff t + 1) := by
  simp only [blockSize, dOff] at hi ⊢
  by_cases ht : t.title = "" <;> cases ed <;> simp [ht] at hi ⊢ <;> omega

theorem visible_attached {w : World} {n : Nat} (h : w.visible n = true) : w.attached n = true := by
  simp only [World.visible, Bool.and_eq_true] at h; exact h.1

/-- The node `n` of a block. -/
theorem DocRep.block_node {m : Model} {w : World} {v5 v7 : String} {lis : List Nat} {c : Nat}
    (hd : DocRep m w v5 v7 lis c) {b n : Nat} {t : TodoR} (hbt : (b, t) ∈ lis.zip m.shown) (hb1 : b ≤ n)
    (hb2 : n < b + blockSize t (decide (m.editingId = t.id))) :
    25 ≤ b ∧ t ∈ m.todos ∧ ∃ v2 ve, w.node n = blockNode b t (decide (m.editingId = t.id)) (some nList) v2 ve (n - b) := by
  have hB := forall₂_zip hd.blocks b t hbt
  obtain ⟨v2, ve, hn⟩ := hB.2
  refine ⟨hd.block_ge hB, (List.mem_filter.1 (List.of_mem_zip hbt).2).1, v2, ve, ?_⟩
  have := hn (n - b) (by omega)
  rwa [show b + (n - b) = n by omega] at this

theorem blockNode_text (b : Nat) (t : TodoR) (ed : Bool) (par : Option Nat) (v2 ve : String) (ht : t.title ≠ "") :
    blockNode b t ed par v2 ve 4 = { tag := "#text", text := t.title, parent := some (b + 3) } := by
  simp [blockNode, ht]

theorem blockNode_dOff (b : Nat) (t : TodoR) (ed : Bool) (par : Option Nat) (v2 ve : String) :
    blockNode b t ed par v2 ve (dOff t) =
      { tag := "button", className := "destroy", parent := some (b + 1),
        listeners := [("click", .fn "destroyTodo" [.num t.id])] } := by
  by_cases ht : t.title = "" <;> simp [blockNode, dOff, ht]

theorem blockNode_edit (b : Nat) (t : TodoR) (par : Option Nat) (v2 ve : String) :
    blockNode b t true par v2 ve (dOff t + 1) =
      { tag := "input", className := "edit", value := ve, parent := some b,
        listeners := [("keydown", .fn "onEditKey" [.num t.id]), ("blur", .fn "onEditBlur" [.num t.id])] } := by
  by_cases ht : t.title = "" <;> simp [blockNode, dOff, ht]

@[simp] theorem finish_hash (m : Model) (id : Int) (title : String) : (m.finish id title).hash = m.hash := by
  unfold Model.finish; split <;> rfl

theorem step_keydown {m : Model} {s : State} (h : Rep m s) (n : Nat) (k : String) :
    ∃ m', Rep m' (app.step s (.keydown n k)) := by
  obtain ⟨v5, v7, lis, c, hd⟩ := h.dom.doc
  simp only [App.step]
  split
  · exact ⟨m, h⟩
  rename_i hv; simp only [Bool.not_eq_true', Bool.not_eq_false] at hv
  have hpre := h.pre
  rcases hd.known_of_attached h.dom.wf (visible_attached hv) with hn | rfl | rfl | rfl | ⟨b, t, hbt, hb1, hb2⟩
  · by_cases h5 : n = nNewTodo
    · subst h5
      rw [fire_one (f := .fn "onNewTodoKey" []) (by simp [nNewTodo, hd.static, staticNode, staticNodeD])]
      have hR := spec_onNewTodoKey (l := none) hpre nNewTodo k
      split at hR
      · exact ⟨_, rep_run_render h.errors (pre_modify_5 hpre "") (by simpa [Model.add] using h.hash)
          (by simpa using h.windowListeners) (h.model.add _) _ (storageRep_save h.storage) hR⟩
      · exact ⟨m, by rw [run_same hR]; exact h⟩
    · rw [fire_nil (by interval_cases n <;> simp_all [hd.static, staticNode, staticNodeD])]
      exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.1])]; exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.2.1])]; exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.2.2])]; exact ⟨m, h⟩
  · obtain ⟨hb25, htm, v2, ve, hn⟩ := hd.block_node hbt hb1 hb2
    have hi := blockNode_cases t (decide (m.editingId = t.id)) (n - b) (by omega)
    rcases hi with hi | hi | hi | hi | ⟨ht, hi⟩ | hi | ⟨he, hi⟩
    pick_goal 7
    · have he' : m.editingId = t.id := by simpa using he
      rw [he] at hn
      rw [fire_one (f := .fn "onEditKey" [.num t.id]) (by rw [hn, hi, blockNode_edit]; simp)]
      have hR := spec_onEditKey (l := none) hpre t.id n k
      split_ifs at hR
      · exact ⟨_, rep_run_render h.errors hpre (by rw [finish_hash]; exact h.hash) h.windowListeners
          (h.model.finish _ _) _ (storageRep_save h.storage) hR⟩
      · rw [setGlobals_eq_withState] at hR
        exact ⟨_, rep_run_render h.errors hpre (by simpa [Model.cancelEdit] using h.hash) h.windowListeners
          h.model.cancelEdit _ (storageRep_same h.storage rfl) hR⟩
      · exact ⟨m, by rw [run_same hR]; exact h⟩
    all_goals (rw [fire_nil (by rw [hn, hi]; first | (rw [blockNode_dOff]; simp) | (rw [blockNode_text _ _ _ _ _ _ ht]; simp) | simp [blockNode])]; exact ⟨m, h⟩)

theorem step_blur {m : Model} {s : State} (h : Rep m s) (n : Nat) :
    ∃ m', Rep m' (app.step s (.blur n)) := by
  obtain ⟨v5, v7, lis, c, hd⟩ := h.dom.doc
  simp only [App.step]
  split
  · exact ⟨m, h⟩
  rename_i hv; simp only [Bool.not_eq_true', Bool.not_eq_false] at hv
  have hpre := h.pre
  rcases hd.known_of_attached h.dom.wf (visible_attached hv) with hn | rfl | rfl | rfl | ⟨b, t, hbt, hb1, hb2⟩
  · rw [fire_nil (by interval_cases n <;> simp_all [hd.static, staticNode, staticNodeD])]
    exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.1])]; exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.2.1])]; exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.2.2])]; exact ⟨m, h⟩
  · obtain ⟨hb25, htm, v2, ve, hn⟩ := hd.block_node hbt hb1 hb2
    have hi := blockNode_cases t (decide (m.editingId = t.id)) (n - b) (by omega)
    rcases hi with hi | hi | hi | hi | ⟨ht, hi⟩ | hi | ⟨he, hi⟩
    pick_goal 7
    · have he' : m.editingId = t.id := by simpa using he
      rw [he] at hn
      rw [fire_one (f := .fn "onEditBlur" [.num t.id]) (by rw [hn, hi, blockNode_edit]; simp)]
      have hR := spec_onEditBlur (l := none) hpre t.id n
      rw [if_pos he'] at hR
      exact ⟨_, rep_run_render h.errors hpre (by rw [finish_hash]; exact h.hash) h.windowListeners
          (h.model.finish _ _) _ (storageRep_save h.storage) hR⟩
    all_goals (rw [fire_nil (by rw [hn, hi]; first | (rw [blockNode_dOff]; simp) | (rw [blockNode_text _ _ _ _ _ _ ht]; simp) | simp [blockNode])]; exact ⟨m, h⟩)

theorem step_dblclick {m : Model} {s : State} (h : Rep m s) (n : Nat) :
    ∃ m', Rep m' (app.step s (.dblclick n)) := by
  obtain ⟨v5, v7, lis, c, hd⟩ := h.dom.doc
  simp only [App.step]
  split
  · exact ⟨m, h⟩
  rename_i hv; simp only [Bool.not_eq_true', Bool.not_eq_false] at hv
  have hpre := h.pre
  rcases hd.known_of_attached h.dom.wf (visible_attached hv) with hn | rfl | rfl | rfl | ⟨b, t, hbt, hb1, hb2⟩
  · rw [fire_nil (by interval_cases n <;> simp_all [hd.static, staticNode, staticNodeD])]
    exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.1])]; exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.2.1])]; exact ⟨m, h⟩
  · rw [fire_nil (by simp [hd.counter.2.2.2])]; exact ⟨m, h⟩
  · obtain ⟨hb25, htm, v2, ve, hn⟩ := hd.block_node hbt hb1 hb2
    have hi := blockNode_cases t (decide (m.editingId = t.id)) (n - b) (by omega)
    rcases hi with hi | hi | hi | hi | ⟨ht, hi⟩ | hi | ⟨he, hi⟩
    pick_goal 4
    · rw [fire_one (f := .fn "startEditing" [.num t.id]) (by rw [hn, hi]; simp [blockNode])]
      have hR := spec_startEditing (l := none) hpre t.id (State.eventObj "dblclick" n "")
      rw [setGlobals_eq_withState] at hR
      exact ⟨_, rep_run_render (m' := m.startEdit t.id) h.errors hpre (by simpa [Model.startEdit] using h.hash) h.windowListeners
          (h.model.startEdit _) _ (storageRep_same h.storage rfl) hR⟩
    pick_goal 6
    · rw [he] at hn
      rw [fire_nil (by rw [hn, hi, blockNode_edit]; simp)]; exact ⟨m, h⟩
    all_goals (rw [fire_nil (by rw [hn, hi]; first | (rw [blockNode_dOff]; simp) | (rw [blockNode_text _ _ _ _ _ _ ht]; simp) | simp [blockNode])]; exact ⟨m, h⟩)

end TodoMVC.Proof
