import LeanTodomvc.Proof.Funcs

/-!
# Lemmas about the worlds produced by rendering
-/

namespace TodoMVC.Proof
open JS DOM World

/-! ## `allocMany` -/

theorem allocMany_same (w : World) (f : Nat → Node) : ∀ n, SameButDom w (allocMany w f n)
  | 0 => .refl w
  | n + 1 => (allocMany_same w f n).trans (.alloc _ _)

@[simp] theorem allocMany_size (w : World) (f : Nat → Node) :
    ∀ n, (allocMany w f n).dom.size = w.dom.size + n
  | 0 => rfl
  | n + 1 => by simp [allocMany, allocMany_size w f n]; omega

theorem allocMany_node (w : World) (f : Nat → Node) :
    ∀ (n k : Nat), (allocMany w f n).node k =
      if k < w.dom.size then w.node k else if k < w.dom.size + n then f (k - w.dom.size) else default
  | 0, k => by
    show w.node k = _
    by_cases h : k < w.dom.size
    · simp [h]
    · simp [h, node_of_size_le w k (by omega)]
  | n + 1, k => by
    show ((allocMany w f n).alloc (f n)).1.node k = _
    rw [node_alloc, allocMany_size, allocMany_node w f n k]
    by_cases h1 : k < w.dom.size
    · have : k ≠ w.dom.size + n := by omega
      simp [h1, this]
    · by_cases h2 : k = w.dom.size + n
      · subst h2; simp; intro h; omega
      · by_cases h3 : k < w.dom.size + n
        · simp [h1, h2, h3, show k < w.dom.size + (n + 1) by omega]
        · simp [h1, h2, h3, show ¬ k < w.dom.size + (n + 1) by omega]

@[simp] theorem renderTodoW_size (w : World) (t : TodoR) (ed : Bool) :
    (renderTodoW w t ed).dom.size = w.dom.size + blockSize t ed := by
  simp [renderTodoW]

theorem renderTodoW_same (w : World) (t : TodoR) (ed : Bool) : SameButDom w (renderTodoW w t ed) :=
  allocMany_same _ _ _

theorem renderTodoW_node_old (w : World) (t : TodoR) (ed : Bool) {k : Nat} (h : k < w.dom.size) :
    (renderTodoW w t ed).node k = w.node k := by
  simp [renderTodoW, allocMany_node, h]

theorem renderTodoW_node_new (w : World) (t : TodoR) (ed : Bool) (i : Nat) (h : i < blockSize t ed) :
    (renderTodoW w t ed).node (w.dom.size + i) = blockNode w.dom.size t ed none "" t.title i := by
  simp [renderTodoW, allocMany_node, h, show ¬ w.dom.size + i < w.dom.size by omega]

theorem blockSize_pos (t : TodoR) (ed : Bool) : 0 < blockSize t ed := by
  simp [blockSize]; omega

@[simp] theorem renderTodoW_li_parent (w : World) (t : TodoR) (ed : Bool) :
    ((renderTodoW w t ed).node w.dom.size).parent = none := by
  have := renderTodoW_node_new w t ed 0 (blockSize_pos t ed)
  simp only [Nat.add_zero] at this
  rw [this]; rfl

/-! ## The `for` loop of `render` -/

/-- Render `t` (if shown) and append it to the list. -/
def attachTodo (m : Model) (w : World) (t : TodoR) : World :=
  if shows (filterStr m.hash) t then
    (renderTodoW w t (decide (m.editingId = t.id))).appendChild nList w.dom.size
  else w

def loopW (m : Model) (ts : List TodoR) (w : World) : World := ts.foldl (attachTodo m) w

theorem attachTodo_same (m : Model) (w : World) (t : TodoR) : SameButDom w (attachTodo m w t) := by
  unfold attachTodo; split
  · exact (renderTodoW_same _ _ _).trans (.appendChild _ _ _)
  · exact .refl w

theorem attachTodo_size_ge (m : Model) (w : World) (t : TodoR) : w.dom.size ≤ (attachTodo m w t).dom.size := by
  unfold attachTodo; split <;> simp

/-- `attachTodo` does not change the parent of existing nodes. -/
theorem attachTodo_parent_old (m : Model) (w : World) (t : TodoR) {k : Nat} (h : k < w.dom.size) :
    ((attachTodo m w t).node k).parent = (w.node k).parent := by
  unfold attachTodo; split
  · rw [appendChild_of_parent_none _ _ _ (renderTodoW_li_parent _ _ _)]
    rw [node_modify, node_modify]
    have hk : ¬ (w.dom.size = k) := by omega
    simp only [hk, false_and, ite_false]
    split <;> simp [renderTodoW_node_old _ _ _ h]
  · rfl

theorem chain_attachTodo {m : Model} {w : World} {t : TodoR} {n : Nat} {l : List Nat}
    (hc : Chain w n l) (hl : ∀ x ∈ l, x < w.dom.size) : Chain (attachTodo m w t) n l :=
  hc.frame fun x hx => attachTodo_parent_old m w t (hl x hx)

/-- The body of `for (const t of todos) { … }` in `render`. -/
def loopBody : List Stmt :=
  [.ite (.call (.var "isShown") [.var "t"])
    [.expr (.call (.member (.var "list") "appendChild") [.call (.var "renderTodo") [.var "t"]])] []]

theorem loopBody_eq : Fn.render.body.getD 1 default = .forOf "t" (.var "todos") loopBody := rfl

/-- The ancestors of the todo list. -/
def listChain : List Nat := [nList, nMain, 1, 0]

theorem mem_listChain {x : Nat} (hx : x ∈ listChain) : x < 25 := by
  have : x = 10 ∨ x = 6 ∨ x = 1 ∨ x = 0 := by simpa [listChain] using hx
  omega

theorem listChain_not_mem {x : Nat} (hx : 25 ≤ x) : listChain.contains x = false := by
  cases h : listChain.contains x
  · rfl
  · have := mem_listChain (by simpa using h); omega

theorem attachTodo_chain {m : Model} {w : World} {t : TodoR} (hc : Chain w nList listChain)
    (hs : 25 ≤ w.dom.size) : Chain (attachTodo m w t) nList listChain :=
  chain_attachTodo hc (fun x hx => by have := mem_listChain hx; omega)

theorem renderTodoW_chain {w : World} {t : TodoR} {ed : Bool} (hc : Chain w nList listChain)
    (hs : 25 ≤ w.dom.size) : Chain (renderTodoW w t ed) nList listChain :=
  hc.frame fun x hx => by
    have := mem_listChain hx
    rw [renderTodoW_node_old _ _ _ (by omega)]

theorem spec_loop (m : Model) : ∀ (ts : List TodoR) (ls : List (String × Value)) (w : World),
    w.funcs = funcs → w.globals = globalsOf m → Chain w nList listChain → 25 ≤ w.dom.size →
    (∀ x, x ≠ "t" → assocGet ls x = none) →
    R (execFor "t" (ts.map TodoR.val) loopBody) (some ls) w =
      some (.ok ((.normal, some (ts.foldl (fun ls t => assocSet ls "t" t.val) ls)), loopW m ts w)) := by
  intro ts
  induction ts with
  | nil => intro ls w _ _ _ _ _; rw [List.map_nil, execFor]; rfl
  | cons t ts ih =>
    intro ls w hf hg hc hs hls
    have hsize : 0 < w.dom.size := by omega
    have hls' : ∀ x, x ≠ "t" → assocGet (assocSet ls "t" t.val) x = none := by
      intro x hx; rw [assocGet_assocSet, if_neg (Ne.symm hx), hls x hx]
    have hloop : loopW m (t :: ts) w = loopW m ts (attachTodo m w t) := rfl
    rw [List.map_cons, List.foldl_cons, hloop, execFor]
    have hat := attachTodo_same m w t
    have ih' := ih _ _ (hat.funcs.trans hf) (hat.globals.trans hg) (attachTodo_chain hc hs)
      (Nat.le_trans hs (attachTodo_size_ge m w t)) hls'
    by_cases hsh : shows (filterStr m.hash) t = true
    · have hanc : (renderTodoW w t (decide (m.editingId = t.id))).ancestors nList = listChain :=
        (renderTodoW_chain hc hs).ancestors_eq (by simp [listChain]; omega)
      have hnc : listChain.contains w.dom.size = false := listChain_not_mem hs
      have hat' : attachTodo m w t =
          (renderTodoW w t (decide (m.editingId = t.id))).appendChild nList w.dom.size := by
        simp [attachTodo, hsh]
      rw [hat'] at ih' ⊢
      js_simp [loopBody, hf, hg, globalsOf, funcs, hls, spec_isShown hf hg, spec_renderTodo hf hg hsize,
        hsh, hanc, hnc]
      exact ih'
    · have hat' : attachTodo m w t = w := by simp [attachTodo, hsh]
      rw [hat'] at ih' ⊢
      js_simp [loopBody, hf, hg, globalsOf, funcs, hls, spec_isShown hf hg, hsh]
      exact ih'

theorem loopW_same (m : Model) : ∀ (ts : List TodoR) (w : World), SameButDom w (loopW m ts w)
  | [], w => .refl w
  | t :: ts, w => (attachTodo_same m w t).trans (loopW_same m ts _)

theorem loopW_size_ge (m : Model) : ∀ (ts : List TodoR) (w : World), w.dom.size ≤ (loopW m ts w).dom.size
  | [], _ => Nat.le_refl _
  | t :: ts, w => Nat.le_trans (attachTodo_size_ge m w t) (loopW_size_ge m ts _)

theorem loopW_parent_old (m : Model) : ∀ (ts : List TodoR) (w : World) (k : Nat), k < w.dom.size →
    ((loopW m ts w).node k).parent = (w.node k).parent
  | [], _, _, _ => rfl
  | t :: ts, w, k, hk => by
    show ((loopW m ts (attachTodo m w t)).node k).parent = _
    rw [loopW_parent_old m ts _ k (Nat.lt_of_lt_of_le hk (attachTodo_size_ge m w t)),
      attachTodo_parent_old m w t hk]

theorem blockNode_parent (b : Nat) (t : TodoR) (ed : Bool) (par : Option Nat) (v2 ve : String)
    (i p : Nat) (h : (blockNode b t ed par v2 ve i).parent = some p) :
    (i = 0 ∧ par = some p) ∨ p < b + i := by
  match i with
  | 0 => left; exact ⟨rfl, h⟩
  | 1 => right; simp [blockNode] at h; omega
  | 2 => right; simp [blockNode] at h; omega
  | 3 => right; simp [blockNode] at h; omega
  | i + 4 =>
    right
    simp only [blockNode] at h
    split_ifs at h <;> cases h <;> omega

theorem parentLt_renderTodoW {w : World} {t : TodoR} {ed : Bool} (h : ParentLt w) :
    ParentLt (renderTodoW w t ed) := by
  refine ⟨fun k p hk => ?_⟩
  unfold renderTodoW at hk
  rw [allocMany_node] at hk
  split at hk
  · exact h.lt k p hk
  · split at hk
    · rcases blockNode_parent _ _ _ _ _ _ _ p hk with ⟨_, h0⟩ | hlt
      · cases h0
      · omega
    · cases hk

theorem parentLt_attachTodo {m : Model} {w : World} {t : TodoR} (h : ParentLt w) (hs : 25 ≤ w.dom.size) :
    ParentLt (attachTodo m w t) := by
  unfold attachTodo; split
  · exact parentLt_appendChild (parentLt_renderTodoW h) (by simp [nList]; omega)
  · exact h

theorem parentLt_loopW (m : Model) : ∀ (ts : List TodoR) (w : World), ParentLt w → 25 ≤ w.dom.size →
    ParentLt (loopW m ts w)
  | [], _, h, _ => h
  | t :: ts, w, h, hs => parentLt_loopW m ts _ (parentLt_attachTodo h hs)
      (Nat.le_trans hs (attachTodo_size_ge m w t))

/-- The indices of the `<li>`s appended by the loop. -/
def lisOf (m : Model) : List TodoR → World → List Nat
  | [], _ => []
  | t :: ts, w => (if shows (filterStr m.hash) t then [w.dom.size] else []) ++ lisOf m ts (attachTodo m w t)

theorem attachTodo_node_old (m : Model) (w : World) (t : TodoR) {k : Nat} (hk : k < w.dom.size) :
    (attachTodo m w t).node k =
      if k = nList ∧ shows (filterStr m.hash) t then
        { w.node k with children := (w.node k).children ++ [w.dom.size] }
      else w.node k := by
  unfold attachTodo
  split
  · rename_i hsh
    rw [appendChild_of_parent_none _ _ _ (renderTodoW_li_parent _ _ _), node_modify, node_modify]
    have hk' : ¬ (w.dom.size = k) := by omega
    simp only [hk', false_and, ite_false, renderTodoW_size]
    by_cases h10 : nList = k
    · subst h10
      simp [hk, renderTodoW_node_old _ _ _ hk, hsh, Nat.lt_add_right]
    · simp [h10, Ne.symm h10, renderTodoW_node_old _ _ _ hk]
  · rename_i hsh; simp [hsh]

theorem loopW_node_old (m : Model) : ∀ (ts : List TodoR) (w : World) (k : Nat), k < w.dom.size →
    (loopW m ts w).node k =
      if k = nList then { w.node k with children := (w.node k).children ++ lisOf m ts w } else w.node k
  | [], w, k, _ => by by_cases h : k = nList <;> simp [loopW, lisOf, h]
  | t :: ts, w, k, hk => by
    show (loopW m ts (attachTodo m w t)).node k = _
    rw [loopW_node_old m ts _ k (Nat.lt_of_lt_of_le hk (attachTodo_size_ge m w t)), attachTodo_node_old m w t hk]
    by_cases h : k = nList
    · subst h; by_cases hsh : shows (filterStr m.hash) t <;> simp [lisOf, hsh]
    · simp [h, lisOf]

/-! ## `render()` -/

def countChain : List Nat := [nCount, nFooter, 1, 0]

theorem mem_countChain {x : Nat} (hx : x ∈ countChain) : x < 25 := by
  have : x = 12 ∨ x = 11 ∨ x = 1 ∨ x = 0 := by simpa [countChain] using hx
  omega

theorem countChain_not_mem {x : Nat} (hx : 25 ≤ x) : countChain.contains x = false := by
  cases h : countChain.contains x
  · rfl
  · have := mem_countChain (by simpa using h); omega

/-- The world after `render()`, step by step as in the JS. (The values are
written the way the JS computes them; `Rep.lean` relates them to the model.) -/
def renderW (m : Model) (w : World) : World :=
  let n : Int := m.activeCount
  let len : Int := m.todos.length
  let w := loopW m m.todos (w.replaceChildren nList)
  let w := w.modify nMain fun nd => { nd with hidden := decide (len = 0) }
  let w := w.modify nFooter fun nd => { nd with hidden := decide (len = 0) }
  let w := w.modify nToggleAll fun nd => { nd with checked := decide (0 < len) && decide (n = 0) }
  let w := w.replaceChildren nCount
  let c := w.dom.size
  let w := (w.alloc { tag := "strong" }).1.setTextContent c (toString n)
  let w := w.appendChild nCount c
  let w := (w.alloc { tag := "#text", text := if n = 1 then " item left" else " items left" }).1.appendChild
    nCount (c + 2)
  let w := w.modify nClear fun nd => { nd with hidden := decide (len - n = 0) }
  let w := w.modify nFilterAll fun nd =>
    { nd with className := if filterStr m.hash = "all" then "selected" else "" }
  let w := w.modify nFilterActive fun nd =>
    { nd with className := if filterStr m.hash = "active" then "selected" else "" }
  w.modify nFilterCompleted fun nd =>
    { nd with className := if filterStr m.hash = "completed" then "selected" else "" }

/-- What `render` needs to know about the world before it runs. -/
structure RenderPre (m : Model) (w : World) : Prop where
  funcs : w.funcs = funcs
  globals : w.globals = globalsOf m
  size : 25 ≤ w.dom.size
  listChain : Chain w nList listChain
  lt : ParentLt w
  listChildren : ∀ c ∈ (w.node nList).children, 25 ≤ c

theorem assocGet_foldl_t (x : String) (hx : x ≠ "t") :
    ∀ (ts : List TodoR) (ls : List (String × Value)),
      assocGet (ts.foldl (fun ls t => assocSet ls "t" t.val) ls) x = assocGet ls x
  | [], _ => rfl
  | t :: ts, ls => by
    rw [List.foldl_cons, assocGet_foldl_t x hx ts, assocGet_assocSet, if_neg (Ne.symm hx)]

set_option maxHeartbeats 8000000 in
theorem spec_render {m : Model} {l : Locals} {w : World} (h : RenderPre m w) :
    R (callValue (.fn "render" []) []) l w = some (.ok ((.undef, l), renderW m w)) := by
  rw [callFn lk_render h.funcs]
  have hc1 : Chain (w.replaceChildren nList) nList listChain :=
    h.listChain.replaceChildren fun x hx hc => by
      have := mem_listChain hx; have := h.listChildren x hc; omega
  have hloop := spec_loop m m.todos [] (w.replaceChildren nList) (by simp [h.funcs]) (by simp [h.globals])
    hc1 (by simp [h.size]) (by intros; rfl)
  unfold loopBody at hloop
  have hW := loopW_same m m.todos (w.replaceChildren nList)
  have hfW : (loopW m m.todos (w.replaceChildren nList)).funcs = funcs := by rw [hW.funcs]; simp [h.funcs]
  have hgW : (loopW m m.todos (w.replaceChildren nList)).globals = globalsOf m := by
    rw [hW.globals]; simp [h.globals]
  have hfil := spec_filterArr (g := .fn "isActive" []) (p := fun t => !t.completed)
    (w := loopW m m.todos (w.replaceChildren nList)) m.todos (fun t _ l => spec_isActive hfW t)
  have hltW : ParentLt (loopW m m.todos (w.replaceChildren nList)) :=
    parentLt_loopW m _ _ (parentLt_replaceChildren h.lt) (by simp [h.size])
  have hsW : 25 ≤ (loopW m m.todos (w.replaceChildren nList)).dom.size :=
    Nat.le_trans (by simp [h.size]) (loopW_size_ge m _ _)
  have hlt12 : nCount < (loopW m m.todos (w.replaceChildren nList)).dom.size := by simp [nCount]; omega
  by_cases hz : m.todos.length = 0
  · have hz' : ((m.todos.length : Int) > 0) = False := by simp [hz]
    js_simp [Fn.render, h.funcs, h.globals, globalsOf, TodoMVC.funcs, todosVal, hloop, hfW, hgW, hfil,
      assocGet_foldl_t, List.length_map, hz', hz, World.ParentLt.not_mem_ancestors, hltW, hlt12,
      parentLt_alloc, parentLt_modify_of, parentLt_modify_parent, parentLt_replaceChildren, Nat.lt_add_right, Option.some.injEq, forall_eq', implies_true,
      forall_const, renderW, Model.activeCount]
    all_goals rfl
  · have hz' : ((m.todos.length : Int) > 0) = True := by simp; omega
    js_simp [Fn.render, h.funcs, h.globals, globalsOf, TodoMVC.funcs, todosVal, hloop, hfW, hgW, hfil,
      assocGet_foldl_t, List.length_map, hz', hz, World.ParentLt.not_mem_ancestors, hltW, hlt12,
      parentLt_alloc, parentLt_modify_of, parentLt_modify_parent, parentLt_replaceChildren, Nat.lt_add_right, Option.some.injEq, forall_eq', implies_true,
      forall_const, renderW, Model.activeCount]
    all_goals rfl

end TodoMVC.Proof
