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

/-! ## Typing into an input field -/

theorem blockNode_tag_input {b : Nat} {t : TodoR} {ed : Bool} {par : Option Nat} {v2 ve : String} {i : Nat}
    (hi : i < blockSize t ed) (ht : (blockNode b t ed par v2 ve i).tag = "input") :
    i = 2 ∨ (ed = true ∧ i = dOff t + 1) := by
  rcases blockNode_cases t ed i hi with rfl | rfl | rfl | rfl | ⟨h4, rfl⟩ | rfl | ⟨he, rfl⟩
  · simp [blockNode] at ht
  · simp [blockNode] at ht
  · left; rfl
  · simp [blockNode] at ht
  · rw [blockNode_text _ _ _ _ _ _ h4] at ht; simp at ht
  · rw [blockNode_dOff] at ht; simp at ht
  · right; exact ⟨he, rfl⟩

theorem blockNode_vals (b : Nat) (t : TodoR) (ed : Bool) (par : Option Nat) (v2 ve v2' ve' : String) (i : Nat)
    (hi : i < blockSize t ed) (h2 : i = 2 → v2' = v2) (he : ed = true → i = dOff t + 1 → ve' = ve) :
    blockNode b t ed par v2' ve' i = blockNode b t ed par v2 ve i := by
  rcases blockNode_cases t ed i hi with rfl | rfl | rfl | rfl | ⟨h4, rfl⟩ | rfl | ⟨he', rfl⟩
  · rfl
  · rfl
  · rw [h2 rfl]; rfl
  · rfl
  · rw [blockNode_text _ _ _ _ _ _ h4, blockNode_text _ _ _ _ _ _ h4]
  · rw [blockNode_dOff, blockNode_dOff]
  · subst he'; rw [he rfl rfl, blockNode_edit, blockNode_edit]

theorem block_modify_value {w : World} {b n : Nat} {t : TodoR} {ed : Bool} {par : Option Nat} (v : String)
    (hB : Block w b t ed par) (ht : (w.node n).tag = "input") :
    Block (w.modify n fun nd => { nd with value := v }) b t ed par := by
  obtain ⟨hs, v2, ve, hn⟩ := hB
  refine ⟨by simpa using hs, if n = b + 2 then v else v2, if n = b + dOff t + 1 then v else ve, fun i hi => ?_⟩
  by_cases hni : n = b + i
  · subst hni
    rw [World.node_modify_self _ _ _ (by omega), hn i hi]
    rw [hn i hi] at ht
    rcases blockNode_tag_input hi ht with rfl | ⟨rfl, rfl⟩
    · simp [blockNode]
    · simp [blockNode_edit, Nat.add_assoc]
  · rw [World.node_modify_ne _ _ _ _ hni, hn i hi]
    exact (blockNode_vals _ _ _ _ _ _ _ _ _ hi (fun h => by subst h; simp [hni])
      (fun _ h => by subst h; simp [Nat.add_assoc, hni])).symm

theorem domRep_modify_value {m : Model} {w : World} {n : Nat} (h : DomRep m w) (ht : (w.node n).tag = "input")
    (v : String) : DomRep m (w.modify n fun nd => { nd with value := v }) := by
  obtain ⟨v5, v7, lis, c, hd⟩ := h.doc
  obtain ⟨hcs, hc0, hc1, hc2⟩ := hd.counter
  have hnc : n ≠ c := by rintro rfl; rw [hc0] at ht; simp at ht
  have hnc1 : n ≠ c + 1 := by rintro rfl; rw [hc1] at ht; simp at ht
  have hnc2 : n ≠ c + 2 := by rintro rfl; rw [hc2] at ht; simp at ht
  refine ⟨by simpa using h.size, ⟨if n = 5 then v else v5, if n = 7 then v else v7, lis, c, ?_, ?_, ?_⟩,
    World.parentWF_modify_of h.wf (fun _ => rfl) (fun _ _ hx => hx),
    World.parentLt_modify_of h.lt (fun _ => rfl)⟩
  · intro k hk
    by_cases hnk : n = k
    · subst hnk
      rw [World.node_modify_self _ _ _ (by have := h.size; omega), hd.static n hk]
      rw [hd.static n hk] at ht
      interval_cases n <;> simp_all [staticNode, staticNodeD, Model.dyn]
    · rw [World.node_modify_ne _ _ _ _ hnk, hd.static k hk]
      interval_cases k <;> simp_all [staticNode, staticNodeD, Model.dyn, Ne.symm hnk]
  · exact hd.blocks.imp fun {_ _} hB => block_modify_value v hB ht
  · refine ⟨by simpa using hcs, ?_, ?_, ?_⟩
    · rw [World.node_modify_ne _ _ _ _ hnc, hc0]
    · rw [World.node_modify_ne _ _ _ _ hnc1, hc1]
    · rw [World.node_modify_ne _ _ _ _ hnc2, hc2]

theorem DocRep.no_input_listener {m : Model} {w : World} {v5 v7 : String} {lis : List Nat} {c : Nat}
    (hd : DocRep m w v5 v7 lis c) {n : Nat} (hk : Known m lis c n) :
    (w.node n).listeners.filter (·.1 == "input") = [] := by
  rcases hk with hn | rfl | rfl | rfl | ⟨b, t, hbt, hb1, hb2⟩
  · interval_cases n <;> simp_all [hd.static, staticNode, staticNodeD]
  · simp [hd.counter.2.1]
  · simp [hd.counter.2.2.1]
  · simp [hd.counter.2.2.2]
  · obtain ⟨hb25, htm, v2, ve, hn⟩ := hd.block_node hbt hb1 hb2
    rw [hn]
    rcases blockNode_cases t (decide (m.editingId = t.id)) (n - b) (by omega) with
      hi | hi | hi | hi | ⟨ht, hi⟩ | hi | ⟨he, hi⟩ <;> rw [hi]
    · simp [blockNode]
    · simp [blockNode]
    · simp [blockNode]
    · simp [blockNode]
    · rw [blockNode_text _ _ _ _ _ _ ht]; simp
    · rw [blockNode_dOff]; simp
    · rw [he, blockNode_edit]; simp

theorem step_input {m : Model} {s : State} (h : Rep m s) (n : Nat) (v : String) :
    ∃ m', Rep m' (app.step s (.input n v)) := by
  obtain ⟨v5, v7, lis, c, hd⟩ := h.dom.doc
  simp only [App.step]
  split
  · exact ⟨m, h⟩
  rename_i hv; simp only [Bool.not_eq_true', Bool.not_eq_false] at hv
  have hk := hd.known_of_attached h.dom.wf (visible_attached hv)
  split
  · exact ⟨m, h⟩
  rename_i ht; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at ht
  refine ⟨m, ?_⟩
  rw [fire_nil]
  · exact { h with dom := domRep_modify_value h.dom ht v }
  simp only [World.node_modify]
  split <;> exact hd.no_input_listener hk

/-! ## Navigation -/

theorem pre_setHash {m : Model} {w : World} (h : Pre m w) (hs : String) : Pre m (w.setHash hs) where
  render := {
    funcs := h.render.funcs, globals := h.render.globals, size := h.render.size
    listChain := (World.chain_setHash _ _ _ _).2 h.render.listChain
    lt := (World.parentLt_setHash _ _).2 h.render.lt
    listChildren := h.render.listChildren }
  wf := (World.parentWF_setHash _ _).2 h.wf
  static := h.static
  count := h.count

theorem rep_setHash {m : Model} {s : State} (h : Rep m s) (hs : String) : ∃ m', Rep m' (s.setHash hs) := by
  unfold State.setHash
  split
  · exact ⟨m, h⟩
  have hpre := pre_setHash h.pre hs
  have hR := spec_route (l := none) hpre [State.eventObj "hashchange" 0]
  simp only [World.setHash_hash] at hR
  rw [setGlobals_eq_withState] at hR
  simp only [World.setHash_windowListeners, h.windowListeners]
  simp
  exact ⟨_, rep_run_render (m' := m.route hs) (s := { s with world := s.world.setHash hs }) h.errors hpre (by simp [Model.route]) (by simpa using h.windowListeners)
    (h.model.route _) _ (storageRep_same h.storage rfl) hR⟩

theorem step_navigate {m : Model} {s : State} (h : Rep m s) (hs : String) :
    ∃ m', Rep m' (app.step s (.navigate hs)) := rep_setHash h hs

/-! ## Clicking -/

theorem pre_toggle_7 {m : Model} {w : World} (h : Pre m w) :
    Pre m (w.modify nToggleAll fun nd => { nd with checked := !nd.checked }) := by
  refine pre_modify h (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) ?_
  obtain ⟨d, hd⟩ := h.static
  refine ⟨{ d with toggleChecked := !d.toggleChecked }, fun k hk => ?_⟩
  by_cases h7 : k = 7
  · subst h7; rw [World.node_modify_self _ _ _ (by have := h.render.size; simp [nToggleAll]; omega), hd 7 hk]; rfl
  · rw [World.node_modify_ne _ _ _ _ (Ne.symm h7), hd k hk]
    interval_cases k <;> first | rfl | exact absurd rfl h7

theorem rep_click {m : Model} {s : State} (h : Rep m s) {v5 v7 : String} {lis : List Nat} {c n : Nat}
    (hd : DocRep m s.world v5 v7 lis c) (hk : Known m lis c n) : ∃ m', Rep m' (s.click n) := by
  have hpre := h.pre
  rcases hk with hn | rfl | rfl | rfl | ⟨b, t, hbt, hb1, hb2⟩
  · by_cases h7 : n = nToggleAll
    · subst h7
      have hpre' := pre_toggle_7 hpre
      have hR := spec_onToggleAll (l := none) hpre' (State.eventObj "click" nToggleAll "")
      simp only [State.click, hd.static nToggleAll (by decide)]
      simp [staticNode, staticNodeD, Node.attr]
      have hsz := h.dom.size
      rw [fire_one (f := .fn "onToggleAll" []) (by
        simp [World.node_modify_self _ _ _ (show nToggleAll < s.world.dom.size by simp [nToggleAll]; omega),
          hd.static nToggleAll (by decide), staticNode, staticNodeD])]
      exact ⟨_, rep_run_render (s := { s with world := s.world.modify nToggleAll fun nd => { nd with checked := !nd.checked } }) h.errors hpre' (by simpa [Model.setAll] using h.hash)
        (by simpa using h.windowListeners) (h.model.setAll _) _ (storageRep_save (by simpa using h.storage)) hR⟩
    by_cases h23 : n = nClear
    · subst h23
      have hR := spec_clearCompleted (l := none) hpre (State.eventObj "click" nClear "")
      simp only [State.click, hd.static nClear (by decide)]
      simp [staticNode, staticNodeD, Node.attr]
      rw [fire_one (f := .fn "clearCompleted" []) (by simp [hd.static nClear (by decide), staticNode, staticNodeD])]
      exact ⟨_, rep_run_render h.errors hpre (by simpa [Model.clear] using h.hash)
        h.windowListeners h.model.clear _ (storageRep_save h.storage) hR⟩
    by_cases hl : n = 15 ∨ n = 18 ∨ n = 21
    · rcases hl with rfl | rfl | rfl
      · simp only [State.click, hd.static 15 (by decide)]
        simp [staticNode, staticNodeD, Node.attr]
        rw [fire_nil (by simp [hd.static 15 (by decide), staticNode, staticNodeD])]
        exact rep_setHash h _
      · simp only [State.click, hd.static 18 (by decide)]
        simp [staticNode, staticNodeD, Node.attr]
        rw [fire_nil (by simp [hd.static 18 (by decide), staticNode, staticNodeD])]
        exact rep_setHash h _
      · simp only [State.click, hd.static 21 (by decide)]
        simp [staticNode, staticNodeD, Node.attr]
        rw [fire_nil (by simp [hd.static 21 (by decide), staticNode, staticNodeD])]
        exact rep_setHash h _
    · refine ⟨m, ?_⟩
      interval_cases n <;> simp_all [State.click, hd.static, staticNode, staticNodeD, Node.attr, State.fire]
  · simp [State.click, hd.counter.2.1, Node.attr, State.fire]; exact ⟨m, h⟩
  · simp [State.click, hd.counter.2.2.1, Node.attr, State.fire]; exact ⟨m, h⟩
  · simp [State.click, hd.counter.2.2.2, Node.attr, State.fire]; exact ⟨m, h⟩
  · obtain ⟨hb25, htm, v2, ve, hn⟩ := hd.block_node hbt hb1 hb2
    have hi := blockNode_cases t (decide (m.editingId = t.id)) (n - b) (by omega)
    rcases hi with hi | hi | hi | hi | ⟨ht, hi⟩ | hi | ⟨he, hi⟩
    · simp [State.click, hn, hi, blockNode, Node.attr, State.fire]; exact ⟨m, h⟩
    · simp [State.click, hn, hi, blockNode, Node.attr, State.fire]; exact ⟨m, h⟩
    · -- the checkbox
      have hn' : n = b + 2 := by omega
      have hsz : n < s.world.dom.size := by have := (forall₂_zip hd.blocks b t hbt).1; rw [hi] at hn; omega
      have hpre' := pre_modify_ge (n := n) (f := fun nd => { nd with checked := !nd.checked }) hpre (by omega)
        (fun _ => rfl) (fun _ => rfl)
      have hR := spec_toggleTodo (l := none) hpre' t.id (State.eventObj "click" n "")
      simp only [State.click, hn, hi]
      simp [blockNode, Node.attr]
      rw [fire_one (f := .fn "toggleTodo" [.num t.id]) (by
        simp [World.node_modify_self _ _ _ hsz, hn, hi, blockNode])]
      exact ⟨_, rep_run_render (s := { s with world := s.world.modify n fun nd => { nd with checked := !nd.checked } })
        h.errors hpre' (by simpa [Model.toggle] using h.hash) (by simpa using h.windowListeners)
        (h.model.toggle _) _ (storageRep_save (by simpa using h.storage)) hR⟩
    · simp [State.click, hn, hi, blockNode, Node.attr, State.fire]; exact ⟨m, h⟩
    · simp [State.click, hn, hi, blockNode_text _ _ _ _ _ _ ht, Node.attr, State.fire]; exact ⟨m, h⟩
    · -- the destroy button
      have hR := spec_destroyTodo (l := none) hpre t.id (State.eventObj "click" n "")
      simp only [State.click, hn, hi, blockNode_dOff]
      simp [Node.attr]
      rw [fire_one (f := .fn "destroyTodo" [.num t.id]) (by simp [hn, hi, blockNode_dOff])]
      exact ⟨_, rep_run_render h.errors hpre (by simpa [Model.destroy] using h.hash)
        h.windowListeners (h.model.destroy _) _ (storageRep_save h.storage) hR⟩
    · rw [he] at hn
      simp [State.click, hn, hi, blockNode_edit, Node.attr, State.fire]; exact ⟨m, h⟩

theorem DocRep.attr_for {m : Model} {w : World} {v5 v7 : String} {lis : List Nat} {c n : Nat}
    (hd : DocRep m w v5 v7 lis c) (hk : Known m lis c n) (h8 : n ≠ 8) : (w.node n).attr "for" = none := by
  rcases hk with hn | rfl | rfl | rfl | ⟨b, t, hbt, hb1, hb2⟩
  · interval_cases n <;> simp_all [hd.static, staticNode, staticNodeD, Node.attr]
  · simp [hd.counter.2.1, Node.attr]
  · simp [hd.counter.2.2.1, Node.attr]
  · simp [hd.counter.2.2.2, Node.attr]
  · obtain ⟨hb25, htm, v2, ve, hn⟩ := hd.block_node hbt hb1 hb2
    rw [hn]
    rcases blockNode_cases t (decide (m.editingId = t.id)) (n - b) (by omega) with
      hi | hi | hi | hi | ⟨ht, hi⟩ | hi | ⟨he, hi⟩ <;> rw [hi]
    · simp [blockNode, Node.attr]
    · simp [blockNode, Node.attr]
    · simp [blockNode, Node.attr]
    · simp [blockNode, Node.attr]
    · rw [blockNode_text _ _ _ _ _ _ ht]; simp [Node.attr]
    · rw [blockNode_dOff]; simp [Node.attr]
    · rw [he, blockNode_edit]; simp [Node.attr]

theorem step_click {m : Model} {s : State} (h : Rep m s) (n : Nat) :
    ∃ m', Rep m' (app.step s (.click n)) := by
  obtain ⟨v5, v7, lis, c, hd⟩ := h.dom.doc
  simp only [App.step]
  split
  · exact ⟨m, h⟩
  rename_i hv; simp only [Bool.not_eq_true', Bool.not_eq_false] at hv
  have hk := hd.known_of_attached h.dom.wf (visible_attached hv)
  by_cases h8 : n = 8
  · subst h8
    have hf : s.world.documentNodes.find? (fun k => (s.world.node k).id == "toggle-all") = some nToggleAll := by
      rw [hd.findId "toggle-all"]
      simp [hd.static, staticNode, staticNodeD]
    simp only [hd.static 8 (by decide)]
    simp [staticNode, staticNodeD, Node.attr, hf]
    exact rep_click h hd (Or.inl (by decide))
  · simp only [hd.attr_for hk h8]
    split
    · contradiction
    · exact rep_click h hd hk

/-- Every action except reloading preserves the representation. -/
theorem step_rep {m : Model} {s : State} (h : Rep m s) (a : Action) (ha : a ≠ .reload) :
    ∃ m', Rep m' (app.step s a) := by
  cases a with
  | click n => exact step_click h n
  | dblclick n => exact step_dblclick h n
  | input n v => exact step_input h n v
  | keydown n k => exact step_keydown h n k
  | blur n => exact step_blur h n
  | navigate hs => exact step_navigate h hs
  | reload => exact absurd rfl ha

end TodoMVC.Proof
