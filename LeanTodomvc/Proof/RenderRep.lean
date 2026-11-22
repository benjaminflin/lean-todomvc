import LeanTodomvc.Proof.Render
import Mathlib.Tactic.IntervalCases

/-!
# The world after `render()` represents the model
-/

namespace TodoMVC.Proof
open JS DOM
open World (node_modify node_alloc node_replaceChildren setTextContent_eq appendChild_of_parent_none
  replaceChildren_of_children_nil parent_modify_of children_modify_of ParentLt Chain ParentWF
  parentWF_alloc parentWF_modify_of parentWF_replaceChildren parentWF_appendChild parentWF_setTextContent
  parentLt_alloc parentLt_modify_of parentLt_replaceChildren parentLt_appendChild parentLt_setTextContent
  lt_size_of_parent)

/-- What `render` does to static node `k`. -/
def renderStatic (m : Model) (w : World) (k : Nat) (nd : Node) : Node :=
  let len : Int := m.todos.length
  let n : Int := m.activeCount
  let S := (loopW m m.todos (w.replaceChildren nList)).dom.size
  if k = nMain ∨ k = nFooter then { nd with hidden := decide (len = 0) }
  else if k = nToggleAll then { nd with checked := decide (0 < len) && decide (n = 0) }
  else if k = nList then { nd with children := lisOf m m.todos (w.replaceChildren nList) }
  else if k = nCount then { nd with children := [S, S + 2] }
  else if k = nClear then { nd with hidden := decide (len - n = 0) }
  else if k = nFilterAll then { nd with className := if filterStr m.hash = "all" then "selected" else "" }
  else if k = nFilterActive then
    { nd with className := if filterStr m.hash = "active" then "selected" else "" }
  else if k = nFilterCompleted then
    { nd with className := if filterStr m.hash = "completed" then "selected" else "" }
  else nd

set_option maxHeartbeats 8000000 in
theorem renderW_node_static {m : Model} {w : World} (h : RenderPre m w)
    (h12 : ∀ c ∈ (w.node nCount).children, 25 ≤ c) (k : Nat) (hk : k < 25) :
    (renderW m w).node k = renderStatic m w k (w.node k) := by
  have hs := loopW_size_ge m m.todos (w.replaceChildren nList)
  have hsz := h.size
  have n10 : ∀ k < 25, k ∉ (w.node 10).children := fun k hk hm => by have := h.listChildren k hm; omega
  have n12 : ∀ k < 25, k ∉ (w.node 12).children := fun k hk hm => by have := h12 k hm; omega
  obtain ⟨S0, hS0⟩ : ∃ S0, w.dom.size = S0 + 25 := ⟨_, (Nat.sub_add_cancel hsz).symm⟩
  obtain ⟨S, hS⟩ : ∃ S, (loopW m m.todos (w.replaceChildren nList)).dom.size = S + 25 :=
    ⟨_, (Nat.sub_add_cancel (Nat.le_trans (by simp [hsz]) hs)).symm⟩
  interval_cases k <;>
  simp [hS, hS0, n10, n12, renderW, renderStatic, node_modify, node_alloc, appendChild_of_parent_none,
    replaceChildren_of_children_nil, parent_modify_of, children_modify_of, node_replaceChildren,
    setTextContent_eq, loopW_node_old, toString_natCast_eq_empty, repr_natCast_eq_empty,
    nMain, nFooter, nToggleAll, nList, nCount, nFilterAll, nFilterActive, nFilterCompleted, nClear]

/-! ## Blocks -/

theorem blockNode_par (b : Nat) (t : TodoR) (ed : Bool) (par par' : Option Nat) (v2 ve : String) (i : Nat)
    (hi : i ≠ 0) : blockNode b t ed par v2 ve i = blockNode b t ed par' v2 ve i := by
  match i, hi with
  | 1, _ | 2, _ | 3, _ => rfl
  | i + 4, _ => rfl

theorem Block.frame {w w' : World} {b : Nat} {t : TodoR} {ed : Bool} {par : Option Nat}
    (h : Block w b t ed par) (hs : w.dom.size ≤ w'.dom.size)
    (hn : ∀ i < blockSize t ed, w'.node (b + i) = w.node (b + i)) : Block w' b t ed par := by
  obtain ⟨hsz, v2, ve, hnodes⟩ := h
  exact ⟨Nat.le_trans hsz hs, v2, ve, fun i hi => (hn i hi).trans (hnodes i hi)⟩

theorem block_attachTodo (m : Model) (w : World) (t : TodoR) (hsh : shows (filterStr m.hash) t = true)
    (hs : 25 ≤ w.dom.size) :
    Block (attachTodo m w t) w.dom.size t (decide (m.editingId = t.id)) (some nList) := by
  have hat : attachTodo m w t =
      (renderTodoW w t (decide (m.editingId = t.id))).appendChild nList w.dom.size := by
    simp [attachTodo, hsh]
  rw [hat, appendChild_of_parent_none _ _ _ (renderTodoW_li_parent _ _ _)]
  refine ⟨by simp, "", t.title, fun i hi => ?_⟩
  rw [node_modify, node_modify]
  have h10 : ¬ (nList = w.dom.size + i) := by simp [nList]; omega
  simp only [h10, false_and, ite_false, renderTodoW_size, renderTodoW_node_new _ _ _ _ hi]
  by_cases h0 : i = 0
  · subst h0; simp [blockNode]; omega
  · have : ¬ (w.dom.size = w.dom.size + i) := by omega
    simp only [this, false_and, ite_false]
    exact blockNode_par _ _ _ _ _ _ _ _ h0

theorem attachTodo_node_ge25 (m : Model) (w : World) (t : TodoR) {k : Nat} (hk : k < w.dom.size)
    (h25 : 25 ≤ k) : (attachTodo m w t).node k = w.node k := by
  rw [attachTodo_node_old m w t hk]
  have : ¬ (k = nList) := by simp [nList]; omega
  simp [this]

theorem loopW_node_ge25 (m : Model) (ts : List TodoR) (w : World) {k : Nat} (hk : k < w.dom.size)
    (h25 : 25 ≤ k) : (loopW m ts w).node k = w.node k := by
  rw [loopW_node_old m ts w k hk]
  have : ¬ (k = nList) := by simp [nList]; omega
  simp [this]

theorem loop_blocks (m : Model) : ∀ (ts : List TodoR) (w : World), 25 ≤ w.dom.size →
    List.Forall₂ (fun b t => Block (loopW m ts w) b t (decide (m.editingId = t.id)) (some nList))
      (lisOf m ts w) (ts.filter (shows (filterStr m.hash)))
  | [], _, _ => by simp [lisOf]
  | t :: ts, w, hs => by
    have hs' : 25 ≤ (attachTodo m w t).dom.size := Nat.le_trans hs (attachTodo_size_ge m w t)
    have ih := loop_blocks m ts (attachTodo m w t) hs'
    by_cases hsh : shows (filterStr m.hash) t = true
    · simp only [lisOf, hsh, ite_true, List.filter_cons, List.singleton_append]
      refine List.Forall₂.cons ?_ ih
      have hb := block_attachTodo m w t hsh hs
      refine hb.frame (loopW_size_ge m ts _) fun i hi => ?_
      apply loopW_node_ge25 m ts _ _ (by omega)
      have := hb.1; omega
    · simp only [lisOf, hsh, List.filter_cons, Bool.false_eq_true, ite_false, List.nil_append]
      exact ih

/-! ## Nodes allocated by the loop are not touched afterwards -/

set_option maxHeartbeats 8000000 in
theorem renderW_node_loop {m : Model} {w : World} (h : RenderPre m w)
    (h12 : ∀ c ∈ (w.node nCount).children, c < w.dom.size) (k : Nat) (hk1 : w.dom.size ≤ k)
    (hk2 : k < (loopW m m.todos (w.replaceChildren nList)).dom.size) :
    (renderW m w).node k = (loopW m m.todos (w.replaceChildren nList)).node k := by
  have hsz := h.size
  generalize hS : (loopW m m.todos (w.replaceChildren nList)).dom.size = S at hk2
  have hk12 : k ∉ (w.node 12).children := fun hm => by have := h12 k hm; omega
  have e1 : ∀ j < 25, (j = k) = False := fun j hj => by simp; omega
  have e2 : ∀ j < 25, (k = j) = False := fun j hj => by simp; omega
  have f1 : (S = k) = False := by simp; omega
  have f2 : (S + 1 = k) = False := by simp; omega
  have f3 : (S + 2 = k) = False := by simp; omega
  have f4 : (k = S) = False := by simp; omega
  have f5 : (k = S + 1) = False := by simp; omega
  have f6 : (k = S + 2) = False := by simp; omega
  have g1 : (k < S) = True := by simp; omega
  have g2 : (12 < w.dom.size) = True := by simp; omega
  have g3 : 12 ∉ (w.node 10).children := fun hm => by have := h.listChildren 12 hm; omega
  simp [hS, hk12, renderW, node_modify, node_alloc, appendChild_of_parent_none,
    replaceChildren_of_children_nil, parent_modify_of, children_modify_of, node_replaceChildren,
    setTextContent_eq, loopW_node_old, toString_natCast_eq_empty, repr_natCast_eq_empty,
    nMain, nFooter, nToggleAll, nList, nCount, nFilterAll, nFilterActive, nFilterCompleted, nClear,
    e1 6 (by omega), e1 7 (by omega), e1 10 (by omega), e1 11 (by omega), e1 12 (by omega),
    e1 15 (by omega), e1 18 (by omega), e1 21 (by omega), e1 23 (by omega),
    e2 6 (by omega), e2 7 (by omega), e2 10 (by omega), e2 11 (by omega), e2 12 (by omega),
    e2 15 (by omega), e2 18 (by omega), e2 21 (by omega), e2 23 (by omega),
    f1, f2, f3, f4, f5, f6, g1, g2, g3, Nat.add_assoc]

/-! ## The counter -/

theorem int_natCast_eq_one (n : Nat) : ((n : Int) = 1) = (n = 1) := by
  simp only [eq_iff_iff]; omega

set_option maxHeartbeats 8000000 in
theorem renderW_counter {m : Model} {w : World} (h : RenderPre m w) :
    Counter (renderW m w) (loopW m m.todos (w.replaceChildren nList)).dom.size m.activeCount := by
  have hsz := h.size
  have hs := loopW_size_ge m m.todos (w.replaceChildren nList)
  generalize hS : (loopW m m.todos (w.replaceChildren nList)).dom.size = S at hs
  simp only [World.size_replaceChildren] at hs
  obtain ⟨S', rfl⟩ : ∃ S', S = S' + 25 := ⟨S - 25, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp [hS, renderW, node_modify, node_alloc, appendChild_of_parent_none,
    replaceChildren_of_children_nil, parent_modify_of, children_modify_of, node_replaceChildren,
    setTextContent_eq, toString_natCast_eq_empty, repr_natCast_eq_empty, countLabel, int_natCast_eq_one,
    nMain, nFooter, nToggleAll, nList, nCount, nFilterAll, nFilterActive, nFilterCompleted, nClear,
    Nat.add_assoc]
  all_goals first | rfl | omega

/-! ## Well-formedness -/

theorem blockNode_parent_mem (b : Nat) (t : TodoR) (ed : Bool) (par : Option Nat) (v2 ve : String)
    (i p : Nat) (hi : i < blockSize t ed) (h : (blockNode b t ed par v2 ve i).parent = some p) (h0 : i ≠ 0) :
    ∃ j < blockSize t ed, p = b + j ∧ b + i ∈ (blockNode b t ed par v2 ve j).children := by
  simp only [blockSize, dOff] at hi
  match i, h0 with
  | 1, _ => refine ⟨0, by simp [blockSize], ?_⟩; simp [blockNode] at h ⊢; omega
  | 2, _ => refine ⟨1, by simp [blockSize, dOff]; omega, ?_⟩; simp [blockNode] at h ⊢; omega
  | 3, _ => refine ⟨1, by simp [blockSize, dOff]; omega, ?_⟩; simp [blockNode] at h ⊢; omega
  | i + 4, _ =>
    simp only [blockNode] at h
    split_ifs at h with h1 h2 h3
    · cases h; refine ⟨3, by simp [blockSize, dOff]; split <;> omega, rfl, ?_⟩
      simp [blockNode, h1.1]; omega
    · cases h; refine ⟨1, by simp [blockSize, dOff]; split <;> omega, rfl, ?_⟩
      simp [blockNode, ← h2]
    · cases h; refine ⟨0, blockSize_pos _ _, by simp, ?_⟩
      simp [blockNode, h3.1]
      try omega
    · cases h

theorem parentWF_renderTodoW {w : World} {t : TodoR} {ed : Bool} (h : ParentWF w) (hl : ParentLt w) :
    ParentWF (renderTodoW w t ed) := by
  refine ⟨fun k p hk => ?_⟩
  unfold renderTodoW at hk ⊢
  rw [allocMany_node] at hk
  split at hk
  · rename_i hks
    have hpk := hl.lt k p hk
    rw [allocMany_node, if_pos (by omega)]
    exact h.wf k p hk
  · rename_i hks
    split at hk
    · rename_i hk2
      obtain ⟨i, rfl⟩ : ∃ i, k = w.dom.size + i := ⟨k - w.dom.size, by omega⟩
      simp only [Nat.add_sub_cancel_left] at hk
      have hi : i < blockSize t ed := by omega
      have h0 : i ≠ 0 := by rintro rfl; cases hk
      obtain ⟨j, hj, rfl, hm⟩ := blockNode_parent_mem _ _ _ _ _ _ _ _ hi hk h0
      rw [allocMany_node, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
      exact hm
    · cases hk

theorem parentWF_attachTodo {m : Model} {w : World} {t : TodoR} (h : ParentWF w) (hl : ParentLt w)
    (hs : 25 ≤ w.dom.size) : ParentWF (attachTodo m w t) := by
  unfold attachTodo; split
  · apply parentWF_appendChild (parentWF_renderTodoW h hl)
    · simp; exact blockSize_pos _ _
    · simp [nList]; omega
  · exact h

theorem parentWF_loopW (m : Model) : ∀ (ts : List TodoR) (w : World), ParentWF w → ParentLt w →
    25 ≤ w.dom.size → ParentWF (loopW m ts w)
  | [], _, h, _, _ => h
  | t :: ts, w, h, hl, hs => parentWF_loopW m ts _ (parentWF_attachTodo h hl hs) (parentLt_attachTodo hl hs)
      (Nat.le_trans hs (attachTodo_size_ge m w t))

/-- Well-formedness is preserved by `modify` with a function which keeps parents and children. -/
theorem wfLt_modify {w : World} {n : Nat} {f : Node → Node} (h : ParentWF w ∧ ParentLt w)
    (hp : ∀ nd, (f nd).parent = nd.parent) (hc : ∀ nd, (f nd).children = nd.children) :
    ParentWF (w.modify n f) ∧ ParentLt (w.modify n f) :=
  ⟨parentWF_modify_of h.1 hp (fun nd x hx => by rw [hc]; exact hx), parentLt_modify_of h.2 hp⟩

theorem tail_wf (W : World) (hW : ParentWF W ∧ ParentLt W) (hs : 25 ≤ W.dom.size)
    (s1 s2 : String) (hs1 : s1 ≠ "") (b : Bool) (c1 c2 c3 : String) :
    let w := W.replaceChildren nCount
    let c := w.dom.size
    let w := (w.alloc { tag := "strong" }).1.setTextContent c s1
    let w := w.appendChild nCount c
    let w := (w.alloc { tag := "#text", text := s2 }).1.appendChild nCount (c + 2)
    let w := w.modify nClear fun nd => { nd with hidden := b }
    let w := w.modify nFilterAll fun nd => { nd with className := c1 }
    let w := w.modify nFilterActive fun nd => { nd with className := c2 }
    let w := w.modify nFilterCompleted fun nd => { nd with className := c3 }
    ParentWF w ∧ ParentLt w := by
  intro w1 c w2 w3 w4 w5 w6 w7 w8
  have e1 : w1.dom.size = W.dom.size := by simp [w1]
  have a1 : ParentWF w1 ∧ ParentLt w1 := ⟨parentWF_replaceChildren hW.1, parentLt_replaceChildren hW.2⟩
  have a2 : ParentWF (w1.alloc { tag := "strong" }).1 ∧ ParentLt (w1.alloc { tag := "strong" }).1 :=
    ⟨parentWF_alloc a1.1 a1.2 (by simp), parentLt_alloc a1.2 (by simp)⟩
  have a3 : ParentWF w2 ∧ ParentLt w2 :=
    ⟨parentWF_setTextContent a2.1 a2.2 (by simp [c]), parentLt_setTextContent a2.2 (by simp [c])⟩
  have e2 : w2.dom.size = c + 2 := by simp [w2, World.size_setTextContent, hs1, c]
  have a4 : ParentWF w3 ∧ ParentLt w3 :=
    ⟨parentWF_appendChild a3.1 (by omega) (by simp [nCount, e2]; omega),
     parentLt_appendChild a3.2 (by simp [c, nCount]; omega)⟩
  have e3 : w3.dom.size = c + 2 := by simp [w3, e2]
  have a5 : ParentWF (w3.alloc { tag := "#text", text := s2 }).1 ∧
      ParentLt (w3.alloc { tag := "#text", text := s2 }).1 :=
    ⟨parentWF_alloc a4.1 a4.2 (by simp), parentLt_alloc a4.2 (by simp)⟩
  have a6 : ParentWF w4 ∧ ParentLt w4 :=
    ⟨parentWF_appendChild a5.1 (by simp [e3]) (by simp [e3, nCount]; omega),
     parentLt_appendChild a5.2 (by simp [c, nCount]; omega)⟩
  exact wfLt_modify (wfLt_modify (wfLt_modify (wfLt_modify a6 (fun _ => rfl) (fun _ => rfl))
    (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl) (fun _ => rfl)

theorem renderW_wf {m : Model} {w : World} (h : RenderPre m w) (hwf : ParentWF w) :
    ParentWF (renderW m w) ∧ ParentLt (renderW m w) := by
  have hl0 : ParentLt (loopW m m.todos (w.replaceChildren nList)) :=
    parentLt_loopW m _ _ (parentLt_replaceChildren h.lt) (by simp [h.size])
  have hw0 : ParentWF (loopW m m.todos (w.replaceChildren nList)) :=
    parentWF_loopW m _ _ (parentWF_replaceChildren hwf) (parentLt_replaceChildren h.lt) (by simp [h.size])
  have hs0 : 25 ≤ (loopW m m.todos (w.replaceChildren nList)).dom.size :=
    Nat.le_trans (by simp [h.size]) (loopW_size_ge m _ _)
  have h3 := wfLt_modify (n := nToggleAll)
    (f := fun nd => { nd with checked := decide (0 < (m.todos.length : Int)) && decide ((m.activeCount : Int) = 0) })
    (wfLt_modify (n := nFooter) (f := fun nd => { nd with hidden := decide ((m.todos.length : Int) = 0) })
      (wfLt_modify (n := nMain) (f := fun nd => { nd with hidden := decide ((m.todos.length : Int) = 0) })
        ⟨hw0, hl0⟩ (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl) (fun _ => rfl)
  exact tail_wf _ h3 (by simpa using hs0) _ _ (by simpa using (toString_natCast_eq_empty _).mp) _ _ _ _

/-! ## Putting it together -/

theorem decide_len_eq_zero (l : List TodoR) : decide ((l.length : Int) = 0) = l.isEmpty := by
  cases l <;> simp; omega

theorem activeCount_eq_zero (l : List TodoR) :
    ((l.filter (!·.completed)).length = 0) ↔ ∀ t ∈ l, t.completed = true := by
  simp [List.filter_eq_nil_iff]

theorem renderStatic_dyn (m : Model) (w : World) (d : Dyn) (k : Nat) (hk : k < 25) :
    renderStatic m w k (staticNodeD d k) =
      staticNodeD (m.dyn d.v5 d.v7 (lisOf m m.todos (w.replaceChildren nList))
        [(loopW m m.todos (w.replaceChildren nList)).dom.size,
         (loopW m m.todos (w.replaceChildren nList)).dom.size + 2]) k := by
  have h1 := decide_len_eq_zero m.todos
  have h2 : (decide (0 < (m.todos.length : Int)) && decide ((m.activeCount : Int) = 0)) = m.allDone := by
    unfold Model.allDone Model.activeCount
    cases hl : m.todos with
    | nil => simp
    | cons t ts =>
      simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and]
      have : (0 : Int) < ((t :: ts).length : Int) := by simp
      simp only [this, decide_true, Bool.true_and, Int.natCast_eq_zero, activeCount_eq_zero]
      simp [List.all_eq]
  have h3 : decide ((m.todos.length : Int) - (m.activeCount : Int) = 0) = !m.todos.any (·.completed) := by
    unfold Model.activeCount
    have hle := List.length_filter_le (fun t : TodoR => !t.completed) m.todos
    have : ((m.todos.length : Int) - ((m.todos.filter (!·.completed)).length : Int) = 0) ↔
        (m.todos.filter (!·.completed)).length = m.todos.length := by omega
    rw [Bool.eq_iff_iff, decide_eq_true_iff, this, List.length_filter_eq_length_iff]
    try simp
  interval_cases k <;>
    simp only [renderStatic, staticNodeD, Model.dyn, selectedIf, nMain, nFooter, nToggleAll, nList, nCount,
      nClear, nFilterAll, nFilterActive, nFilterCompleted, Nat.reduceEqDiff, reduceIte, or_self, or_false,
      false_or, or_true, h1, h2, h3, decide_eq_true_eq, ite_false, ite_true]

theorem lisOf_ge (m : Model) : ∀ (ts : List TodoR) (w : World), ∀ b ∈ lisOf m ts w, w.dom.size ≤ b
  | [], _, b, hb => by simp [lisOf] at hb
  | t :: ts, w, b, hb => by
    simp only [lisOf, List.mem_append] at hb
    rcases hb with hb | hb
    · split at hb
      · simp at hb; omega
      · simp at hb
    · exact Nat.le_trans (attachTodo_size_ge m w t) (lisOf_ge m ts _ b hb)

/-- `render()` re-establishes the representation of the document. -/
theorem domRep_renderW {m : Model} {w : World} {d : Dyn} (h : RenderPre m w) (hwf : ParentWF w)
    (hst : ∀ k < 25, w.node k = staticNodeD d k)
    (h12 : ∀ c ∈ (w.node nCount).children, 25 ≤ c ∧ c < w.dom.size) :
    DomRep m (renderW m w) := by
  have hc := renderW_counter h
  obtain ⟨hwf', hlt'⟩ := renderW_wf h hwf
  have hS := loopW_size_ge m m.todos (w.replaceChildren nList)
  refine ⟨?_, ?_, hwf', hlt'⟩
  · have := hc.1; have := h.size; simp at hS; omega
  · refine ⟨d.v5, d.v7, lisOf m m.todos (w.replaceChildren nList),
      (loopW m m.todos (w.replaceChildren nList)).dom.size, ?_, ?_, hc⟩
    · intro k hk
      rw [renderW_node_static h (fun c hc => (h12 c hc).1) k hk, hst k hk, renderStatic_dyn m w d k hk]
      rfl
    · have hb := loop_blocks m m.todos (w.replaceChildren nList) (by simp [h.size])
      have hge := lisOf_ge m m.todos (w.replaceChildren nList)
      have hb2 : List.Forall₂ (fun b t => (w.dom.size ≤ b) ∧
          Block (loopW m m.todos (w.replaceChildren nList)) b t (decide (m.editingId = t.id)) (some nList))
          (lisOf m m.todos (w.replaceChildren nList)) m.shown :=
        (List.forall₂_and_left _ _).mpr ⟨fun b hb' => by simpa using hge b hb', hb⟩
      refine hb2.imp fun b t ⟨hbge, hbl⟩ => hbl.frame (by
        have := hc.1; omega) fun i hi => ?_
      apply renderW_node_loop h (fun c hc => (h12 c hc).2) _ (by omega)
      have := hbl.1; omega

end TodoMVC.Proof
