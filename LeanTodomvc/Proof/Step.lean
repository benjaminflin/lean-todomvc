import LeanTodomvc.Proof.Observe

/-!
# Every action preserves the representation
-/

namespace TodoMVC.Proof
open JS DOM
open World (ParentWF ParentLt Chain SameButDom)

theorem run_fire1 (s : State) (f ev : Value) {v : Value} {l : Locals} {w' : World}
    (h : R (callValue f [ev]) none s.world = some (.ok ((v, l), w'))) :
    s.run (fireListeners [f] ev) = { s with world := w' } := by
  have : R (fireListeners [f] ev) none s.world = some (.ok (((), l), w')) := by
    simp [fireListeners, h, Res.andThen]
  simp only [State.run, M.run']
  simp only [R] at this
  rw [this]

theorem renderW_same (m : Model) (w : World) : SameButDom w (renderW m w) := by
  unfold renderW
  exact ((((((((((((((SameButDom.replaceChildren _ _).trans (loopW_same _ _ _)).trans (.modify _ _ _)).trans
    (.modify _ _ _)).trans (.modify _ _ _)).trans (.replaceChildren _ _)).trans (.alloc _ _)).trans
    (.setTextContent _ _ _)).trans (.appendChild _ _ _)).trans (.alloc _ _)).trans (.appendChild _ _ _)).trans
    (.modify _ _ _)).trans (.modify _ _ _)).trans (.modify _ _ _)).trans (.modify _ _ _)

theorem forall₂_left {α β} {R : α → β → Prop} {P : α → Prop} (hp : ∀ a b, R a b → P a) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, P a
  | _, _, .nil => by simp
  | _, _, .cons hab hr => by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hp _ _ hab
    · exact forall₂_left hp hr a ha

section
variable {m : Model} {w : World} {v5 v7 : String} {lis : List Nat} {c : Nat} (h : DocRep m w v5 v7 lis c)
include h

theorem DocRep.block_ge {b : Nat} {t : TodoR} {ed : Bool} (hb : Block w b t ed (some nList)) : 25 ≤ b := by
  obtain ⟨v2, ve, hn⟩ := hb.2
  have h0 := hn 0 (by simp only [blockSize, dOff]; split <;> split <;> omega)
  simp only [Nat.add_zero] at h0
  by_contra hlt
  have hst := h.static b (by omega)
  rw [hst] at h0
  interval_cases b <;> simp [staticNode, staticNodeD, blockNode] at h0

theorem DocRep.lis_ge : ∀ b ∈ lis, 25 ≤ b :=
  forall₂_left (fun _ _ hb => h.block_ge hb) h.blocks

theorem DocRep.counter_ge : 25 ≤ c := by
  have h0 := h.counter.2.1
  by_contra hlt
  have hst := h.static c (by omega)
  rw [hst] at h0
  interval_cases c <;> simp [staticNode, staticNodeD] at h0

end

theorem Rep.pre {m : Model} {s : State} (h : Rep m s) : Pre m s.world := by
  obtain ⟨v5, v7, lis, c, hd⟩ := h.dom.doc
  have hc := hd.counter_ge
  refine ⟨⟨h.funcs, h.globals, hd.size, ?_, h.dom.lt, ?_⟩, h.dom.wf, ⟨_, hd.static⟩, ?_⟩
  · have := hd.static
    exact .step (by simp [nList, hd.static, staticNode, staticNodeD]) <|
      .step (by simp [nMain, hd.static, staticNode, staticNodeD]) <|
      .step (by simp [hd.static, staticNode, staticNodeD]) <|
      .root (by simp [hd.static, staticNode, staticNodeD])
  · rw [hd.items]; exact hd.lis_ge
  · have := hd.counter.1
    simp [nCount, hd.static, staticNode, staticNodeD, Model.dyn]
    omega

theorem rep_renderW {m m' : Model} {w : World} (h : Pre m w) (hwf : m'.WF) (st : List (String × String))
    (hst : storageRep m' st) (hh : w.hash = m'.hash)
    (hwl : w.windowListeners = [("hashchange", .fn "route" [])]) :
    Rep m' { world := renderW m' (withState w (globalsOf m') st) } := by
  have h' : Pre m' (withState w (globalsOf m') st) := pre_withState h st
  obtain ⟨d, hd⟩ := h'.static
  have hs := renderW_same m' (withState w (globalsOf m') st)
  exact {
    errors := rfl
    funcs := by rw [hs.funcs]; exact h'.render.funcs
    globals := by rw [hs.globals]; exact h'.render.globals
    hash := by rw [hs.hash]; simpa using hh
    windowListeners := by rw [hs.windowListeners]; simpa using hwl
    storage := by rw [hs.storage]; simpa using hst
    model := hwf
    dom := domRep_renderW h'.render h'.wf hd h'.count }

theorem pre_modify {m : Model} {w : World} {n : Nat} {f : Node → Node} (h : Pre m w)
    (hp : ∀ nd, (f nd).parent = nd.parent) (hc : ∀ nd, (f nd).children = nd.children)
    (hn10 : n ≠ nList) (hn12 : n ≠ nCount) (hs : ∃ d, ∀ k < 25, (w.modify n f).node k = staticNodeD d k) :
    Pre m (w.modify n f) where
  render := {
    funcs := h.render.funcs, globals := h.render.globals, size := by simpa using h.render.size
    listChain := (World.chain_modify_iff hp _ _).2 h.render.listChain
    lt := World.parentLt_modify_of h.render.lt hp
    listChildren := by rw [World.node_modify_ne _ _ _ _ hn10]; exact h.render.listChildren }
  wf := World.parentWF_modify_of h.wf hp (fun nd x hx => by rw [hc]; exact hx)
  static := hs
  count := by rw [World.node_modify_ne _ _ _ _ hn12, World.size_modify]; exact h.count

theorem pre_modify_ge {m : Model} {w : World} {n : Nat} {f : Node → Node} (h : Pre m w) (hn : 25 ≤ n)
    (hp : ∀ nd, (f nd).parent = nd.parent) (hc : ∀ nd, (f nd).children = nd.children) :
    Pre m (w.modify n f) := by
  refine pre_modify h hp hc (by simp [nList]; omega) (by simp [nCount]; omega) ?_
  obtain ⟨d, hd⟩ := h.static
  exact ⟨d, fun k hk => by rw [World.node_modify_ne _ _ _ _ (by omega)]; exact hd k hk⟩

/-- Editing the new-todo field. -/
theorem pre_modify_5 {m : Model} {w : World} (h : Pre m w) (v : String) :
    Pre m (w.modify nNewTodo fun nd => { nd with value := v }) := by
  refine pre_modify h (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) ?_
  obtain ⟨d, hd⟩ := h.static
  refine ⟨{ d with v5 := v }, fun k hk => ?_⟩
  by_cases h5 : k = 5
  · subst h5; rw [World.node_modify_self _ _ _ (by have := h.render.size; simp [nNewTodo]; omega), hd 5 hk]; rfl
  · rw [World.node_modify_ne _ _ _ _ (Ne.symm h5), hd k hk]
    interval_cases k <;> first | rfl | exact absurd rfl h5

/-- Editing or toggling the toggle-all checkbox. -/
theorem pre_modify_7 {m : Model} {w : World} (h : Pre m w) (v : String) (b : Bool → Bool) :
    Pre m (w.modify nToggleAll fun nd => { nd with value := v, checked := b nd.checked }) := by
  refine pre_modify h (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) ?_
  obtain ⟨d, hd⟩ := h.static
  refine ⟨{ d with v7 := v, toggleChecked := b d.toggleChecked }, fun k hk => ?_⟩
  by_cases h7 : k = 7
  · subst h7; rw [World.node_modify_self _ _ _ (by have := h.render.size; simp [nToggleAll]; omega), hd 7 hk]; rfl
  · rw [World.node_modify_ne _ _ _ _ (Ne.symm h7), hd k hk]
    interval_cases k <;> first | rfl | exact absurd rfl h7

/-! ## Storage and model well-formedness -/

theorem storageRep_save {m m' : Model} {st : List (String × String)} (h : storageRep m st) :
    storageRep m' (saveStorage m' st) := by
  right
  rcases h with ⟨rfl, -⟩ | rfl
  · rfl
  · simp [saveStorage, assocSet_cons]

theorem storageRep_same {m m' : Model} {st : List (String × String)} (h : storageRep m st)
    (ht : m'.todos = m.todos) : storageRep m' st := by
  unfold storageRep; rw [ht]; exact h

theorem setGlobals_eq_withState (w : World) (g : List (String × Value)) :
    w.setGlobals g = withState w g w.storage := by cases w; rfl

theorem Model.WF.map_id {m m' : Model} (h : m.WF) (f : TodoR → TodoR) (hf : ∀ t, (f t).id = t.id)
    (ht : m'.todos = m.todos.map f) (hn : m'.nextId = m.nextId) : m'.WF := by
  have hid : (m.todos.map f).map (·.id) = m.todos.map (·.id) := by
    simp [List.map_map, Function.comp_def, hf]
  refine ⟨by rw [ht, hid]; exact h.nodup, ?_, ?_, ?_⟩
  · intro t ht'; rw [ht] at ht'; obtain ⟨t0, h0, rfl⟩ := List.mem_map.1 ht'; rw [hf]; exact h.nonneg t0 h0
  · intro t ht'; rw [ht] at ht'; obtain ⟨t0, h0, rfl⟩ := List.mem_map.1 ht'; rw [hf, hn]; exact h.lt t0 h0
  · rw [hn]; exact h.nextId_nonneg

theorem Model.WF.filter {m m' : Model} (h : m.WF) (p : TodoR → Bool)
    (ht : m'.todos = m.todos.filter p) (hn : m'.nextId = m.nextId) : m'.WF := by
  refine ⟨by rw [ht]; exact h.nodup.sublist (List.Sublist.map _ List.filter_sublist), ?_, ?_, ?_⟩
  · intro t ht'; rw [ht] at ht'; exact h.nonneg t ((List.mem_filter.1 ht').1)
  · intro t ht'; rw [ht, hn] at *; exact h.lt t ((List.mem_filter.1 ht').1)
  · rw [hn]; exact h.nextId_nonneg

theorem Model.WF.toggle {m : Model} (h : m.WF) (id : Int) : (m.toggle id).WF :=
  h.map_id _ (fun t => by split <;> rfl) rfl rfl

theorem Model.WF.destroy {m : Model} (h : m.WF) (id : Int) : (m.destroy id).WF := h.filter _ rfl rfl

theorem Model.WF.clear {m : Model} (h : m.WF) : m.clear.WF := h.filter _ rfl rfl

theorem Model.WF.setAll {m : Model} (h : m.WF) (c : Bool) : (m.setAll c).WF :=
  h.map_id (fun t => { t with completed := c }) (fun _ => rfl) rfl rfl

theorem Model.WF.startEdit {m : Model} (h : m.WF) (id : Int) : (m.startEdit id).WF :=
  h.map_id _root_.id (fun _ => rfl) (by simp [Model.startEdit]) rfl

theorem Model.WF.cancelEdit {m : Model} (h : m.WF) : m.cancelEdit.WF := h.map_id id (fun _ => rfl) (by simp [Model.cancelEdit]) rfl

theorem Model.WF.route {m : Model} (h : m.WF) (hs : String) : (m.route hs).WF := h.map_id id (fun _ => rfl) (by simp [Model.route]) rfl

theorem Model.WF.finish {m : Model} (h : m.WF) (id : Int) (title : String) : (m.finish id title).WF := by
  unfold Model.finish; split
  · exact h.filter _ rfl rfl
  · exact h.map_id _ (fun t => by split <;> rfl) rfl rfl

theorem Model.WF.add {m : Model} (h : m.WF) (title : String) : (m.add title).WF := by
  have hn := h.nextId_nonneg
  refine ⟨?_, ?_, ?_, by simp [Model.add]; omega⟩
  · simp only [Model.add, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨h.nodup, by simp, ?_⟩
    simp only [List.mem_map, List.mem_singleton]
    rintro a ⟨t, ht, rfl⟩ b rfl hab
    have := h.lt t ht; omega
  · intro t ht; simp [Model.add] at ht
    rcases ht with ht | rfl
    · exact h.nonneg t ht
    · exact hn
  · intro t ht; simp [Model.add] at ht ⊢
    rcases ht with ht | rfl
    · have := h.lt t ht; omega
    · simp

end TodoMVC.Proof
