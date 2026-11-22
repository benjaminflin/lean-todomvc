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

end TodoMVC.Proof
