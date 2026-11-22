import LeanTodomvc.DOM

/-!
# Lemmas about DOM operations

The DOM operations only change the `dom` field of the world.
-/

namespace World
open DOM

@[simp] theorem alloc_fst_globals (w : World) (nd : Node) : (w.alloc nd).1.globals = w.globals := rfl
@[simp] theorem alloc_fst_funcs (w : World) (nd : Node) : (w.alloc nd).1.funcs = w.funcs := rfl
@[simp] theorem alloc_fst_storage (w : World) (nd : Node) : (w.alloc nd).1.storage = w.storage := rfl
@[simp] theorem alloc_fst_hash (w : World) (nd : Node) : (w.alloc nd).1.hash = w.hash := rfl
@[simp] theorem alloc_fst_windowListeners (w : World) (nd : Node) :
    (w.alloc nd).1.windowListeners = w.windowListeners := rfl
@[simp] theorem alloc_fst_dom (w : World) (nd : Node) : (w.alloc nd).1.dom = w.dom.push nd := rfl
@[simp] theorem alloc_snd (w : World) (nd : Node) : (w.alloc nd).2 = w.dom.size := rfl

@[simp] theorem modify_globals (w : World) n f : (w.modify n f).globals = w.globals := rfl
@[simp] theorem modify_funcs (w : World) n f : (w.modify n f).funcs = w.funcs := rfl
@[simp] theorem modify_storage (w : World) n f : (w.modify n f).storage = w.storage := rfl
@[simp] theorem modify_hash (w : World) n f : (w.modify n f).hash = w.hash := rfl
@[simp] theorem modify_windowListeners (w : World) n f :
    (w.modify n f).windowListeners = w.windowListeners := rfl
@[simp] theorem modify_dom (w : World) n f : (w.modify n f).dom = w.dom.modify n f := rfl

/-- `w'` differs from `w` at most in the DOM. -/
structure SameButDom (w w' : World) : Prop where
  globals : w'.globals = w.globals
  funcs : w'.funcs = w.funcs
  storage : w'.storage = w.storage
  hash : w'.hash = w.hash
  windowListeners : w'.windowListeners = w.windowListeners

theorem SameButDom.refl (w : World) : SameButDom w w := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SameButDom.trans {w₁ w₂ w₃ : World} (h₁ : SameButDom w₁ w₂) (h₂ : SameButDom w₂ w₃) :
    SameButDom w₁ w₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2, h₂.3.trans h₁.3, h₂.4.trans h₁.4, h₂.5.trans h₁.5⟩

theorem SameButDom.modify (w : World) n f : SameButDom w (w.modify n f) := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SameButDom.alloc (w : World) nd : SameButDom w (w.alloc nd).1 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SameButDom.detach (w : World) c : SameButDom w (w.detach c) := by
  unfold World.detach; split
  · exact .refl w
  · exact (SameButDom.modify _ _ _).trans (SameButDom.modify _ _ _)

theorem SameButDom.appendChild (w : World) p c : SameButDom w (w.appendChild p c) :=
  (((SameButDom.detach w c).trans (.modify _ _ _)).trans (.modify _ _ _))

theorem SameButDom.foldl_modify (cs : List Nat) (f : Nat → Node → Node) :
    ∀ w, SameButDom w (cs.foldl (fun w c => w.modify c (f c)) w) := by
  induction cs with
  | nil => exact .refl
  | cons c cs ih => intro w; exact (SameButDom.modify w c (f c)).trans (ih _)

theorem SameButDom.replaceChildren (w : World) p : SameButDom w (w.replaceChildren p) := by
  unfold World.replaceChildren
  exact (SameButDom.foldl_modify _ (fun _ nd => { nd with parent := none }) w).trans (.modify _ _ _)

theorem SameButDom.setTextContent (w : World) n s : SameButDom w (w.setTextContent n s) := by
  unfold World.setTextContent
  split
  · exact .replaceChildren w n
  · exact ((SameButDom.replaceChildren w n).trans (.alloc _ _)).trans (.appendChild _ _ _)

@[simp] theorem detach_globals (w : World) (c : Nat) : (w.detach c).globals = w.globals :=
  (SameButDom.detach w c).globals
@[simp] theorem detach_funcs (w : World) (c : Nat) : (w.detach c).funcs = w.funcs :=
  (SameButDom.detach w c).funcs
@[simp] theorem detach_storage (w : World) (c : Nat) : (w.detach c).storage = w.storage :=
  (SameButDom.detach w c).storage
@[simp] theorem detach_hash (w : World) (c : Nat) : (w.detach c).hash = w.hash :=
  (SameButDom.detach w c).hash
@[simp] theorem detach_windowListeners (w : World) (c : Nat) : (w.detach c).windowListeners = w.windowListeners :=
  (SameButDom.detach w c).windowListeners
@[simp] theorem appendChild_globals (w : World) (p c : Nat) : (w.appendChild p c).globals = w.globals :=
  (SameButDom.appendChild w p c).globals
@[simp] theorem appendChild_funcs (w : World) (p c : Nat) : (w.appendChild p c).funcs = w.funcs :=
  (SameButDom.appendChild w p c).funcs
@[simp] theorem appendChild_storage (w : World) (p c : Nat) : (w.appendChild p c).storage = w.storage :=
  (SameButDom.appendChild w p c).storage
@[simp] theorem appendChild_hash (w : World) (p c : Nat) : (w.appendChild p c).hash = w.hash :=
  (SameButDom.appendChild w p c).hash
@[simp] theorem appendChild_windowListeners (w : World) (p c : Nat) : (w.appendChild p c).windowListeners = w.windowListeners :=
  (SameButDom.appendChild w p c).windowListeners
@[simp] theorem replaceChildren_globals (w : World) (p : Nat) : (w.replaceChildren p).globals = w.globals :=
  (SameButDom.replaceChildren w p).globals
@[simp] theorem replaceChildren_funcs (w : World) (p : Nat) : (w.replaceChildren p).funcs = w.funcs :=
  (SameButDom.replaceChildren w p).funcs
@[simp] theorem replaceChildren_storage (w : World) (p : Nat) : (w.replaceChildren p).storage = w.storage :=
  (SameButDom.replaceChildren w p).storage
@[simp] theorem replaceChildren_hash (w : World) (p : Nat) : (w.replaceChildren p).hash = w.hash :=
  (SameButDom.replaceChildren w p).hash
@[simp] theorem replaceChildren_windowListeners (w : World) (p : Nat) : (w.replaceChildren p).windowListeners = w.windowListeners :=
  (SameButDom.replaceChildren w p).windowListeners
@[simp] theorem setTextContent_globals (w : World) (n : Nat) (t : String) : (w.setTextContent n t).globals = w.globals :=
  (SameButDom.setTextContent w n t).globals
@[simp] theorem setTextContent_funcs (w : World) (n : Nat) (t : String) : (w.setTextContent n t).funcs = w.funcs :=
  (SameButDom.setTextContent w n t).funcs
@[simp] theorem setTextContent_storage (w : World) (n : Nat) (t : String) : (w.setTextContent n t).storage = w.storage :=
  (SameButDom.setTextContent w n t).storage
@[simp] theorem setTextContent_hash (w : World) (n : Nat) (t : String) : (w.setTextContent n t).hash = w.hash :=
  (SameButDom.setTextContent w n t).hash
@[simp] theorem setTextContent_windowListeners (w : World) (n : Nat) (t : String) : (w.setTextContent n t).windowListeners = w.windowListeners :=
  (SameButDom.setTextContent w n t).windowListeners

/-! ## Setters -/

section setters
variable (w : World)
@[simp] theorem setGlobals_dom g : (w.setGlobals g).dom = w.dom := rfl
@[simp] theorem setGlobals_globals g : (w.setGlobals g).globals = g := rfl
@[simp] theorem setGlobals_funcs g : (w.setGlobals g).funcs = w.funcs := rfl
@[simp] theorem setGlobals_storage g : (w.setGlobals g).storage = w.storage := rfl
@[simp] theorem setGlobals_hash g : (w.setGlobals g).hash = w.hash := rfl
@[simp] theorem setGlobals_windowListeners g : (w.setGlobals g).windowListeners = w.windowListeners := rfl
@[simp] theorem setStorage_dom st : (w.setStorage st).dom = w.dom := rfl
@[simp] theorem setStorage_globals st : (w.setStorage st).globals = w.globals := rfl
@[simp] theorem setStorage_funcs st : (w.setStorage st).funcs = w.funcs := rfl
@[simp] theorem setStorage_storage st : (w.setStorage st).storage = st := rfl
@[simp] theorem setStorage_hash st : (w.setStorage st).hash = w.hash := rfl
@[simp] theorem setStorage_windowListeners st : (w.setStorage st).windowListeners = w.windowListeners := rfl
@[simp] theorem setHash_dom h : (w.setHash h).dom = w.dom := rfl
@[simp] theorem setHash_globals h : (w.setHash h).globals = w.globals := rfl
@[simp] theorem setHash_funcs h : (w.setHash h).funcs = w.funcs := rfl
@[simp] theorem setHash_storage h : (w.setHash h).storage = w.storage := rfl
@[simp] theorem setHash_hash h : (w.setHash h).hash = h := rfl
@[simp] theorem setHash_windowListeners h : (w.setHash h).windowListeners = w.windowListeners := rfl
@[simp] theorem setGlobals_node g k : (w.setGlobals g).node k = w.node k := rfl
@[simp] theorem setStorage_node st k : (w.setStorage st).node k = w.node k := rfl
@[simp] theorem setHash_node h k : (w.setHash h).node k = w.node k := rfl
@[simp] theorem setFuncs_dom fs : (w.setFuncs fs).dom = w.dom := rfl
@[simp] theorem setFuncs_globals fs : (w.setFuncs fs).globals = w.globals := rfl
@[simp] theorem setFuncs_funcs fs : (w.setFuncs fs).funcs = fs := rfl
@[simp] theorem setFuncs_storage fs : (w.setFuncs fs).storage = w.storage := rfl
@[simp] theorem setFuncs_hash fs : (w.setFuncs fs).hash = w.hash := rfl
@[simp] theorem setFuncs_windowListeners fs : (w.setFuncs fs).windowListeners = w.windowListeners := rfl
@[simp] theorem setFuncs_node fs k : (w.setFuncs fs).node k = w.node k := rfl
@[simp] theorem setWindowListeners_dom ls : (w.setWindowListeners ls).dom = w.dom := rfl
@[simp] theorem setWindowListeners_globals ls : (w.setWindowListeners ls).globals = w.globals := rfl
@[simp] theorem setWindowListeners_funcs ls : (w.setWindowListeners ls).funcs = w.funcs := rfl
@[simp] theorem setWindowListeners_storage ls : (w.setWindowListeners ls).storage = w.storage := rfl
@[simp] theorem setWindowListeners_hash ls : (w.setWindowListeners ls).hash = w.hash := rfl
@[simp] theorem setWindowListeners_windowListeners ls :
    (w.setWindowListeners ls).windowListeners = ls := rfl
@[simp] theorem setWindowListeners_node ls k : (w.setWindowListeners ls).node k = w.node k := rfl
end setters

/-! ## Nodes -/

@[simp] theorem size_modify (w : World) n f : (w.modify n f).dom.size = w.dom.size := Array.size_modify

theorem node_eq (w : World) (k : Nat) : w.node k = (w.dom[k]?).getD default := rfl

theorem node_modify (w : World) (n : Nat) (f : Node → Node) (k : Nat) :
    (w.modify n f).node k = if n = k ∧ k < w.dom.size then f (w.node k) else w.node k := by
  simp only [node_eq, modify_dom, Array.getElem?_modify]
  by_cases h : n = k
  · subst h
    by_cases hk : n < w.dom.size
    · simp [hk, Array.getElem?_eq_getElem hk]
    · simp [hk, Array.getElem?_eq_none (Nat.le_of_not_lt hk)]
  · simp [h]

@[simp] theorem node_modify_self (w : World) (n : Nat) (f : Node → Node) (h : n < w.dom.size) :
    (w.modify n f).node n = f (w.node n) := by
  simp [node_modify, h]

@[simp] theorem node_modify_ne (w : World) (n k : Nat) (f : Node → Node) (h : n ≠ k) :
    (w.modify n f).node k = w.node k := by
  simp [node_modify, h]

theorem parent_modify_of (w : World) (n : Nat) (f : Node → Node) (k : Nat)
    (hf : ∀ nd, (f nd).parent = nd.parent) : ((w.modify n f).node k).parent = (w.node k).parent := by
  rw [node_modify]; split <;> simp [hf]

theorem children_modify_of (w : World) (n : Nat) (f : Node → Node) (k : Nat)
    (hf : ∀ nd, (f nd).children = nd.children) :
    ((w.modify n f).node k).children = (w.node k).children := by
  rw [node_modify]; split <;> simp [hf]

theorem node_alloc (w : World) (nd : Node) (k : Nat) :
    (w.alloc nd).1.node k = if k = w.dom.size then nd else w.node k := by
  simp only [node_eq, alloc_fst_dom, Array.getElem?_push]
  split <;> simp

@[simp] theorem node_alloc_new (w : World) (nd : Node) : (w.alloc nd).1.node w.dom.size = nd := by
  simp [node_alloc]

theorem node_alloc_eq (w : World) (nd : Node) (k : Nat) (h : k = w.dom.size) :
    (w.alloc nd).1.node k = nd := by
  subst h; simp [node_alloc]

@[simp] theorem node_alloc_old (w : World) (nd : Node) (k : Nat) (h : k ≠ w.dom.size) :
    (w.alloc nd).1.node k = w.node k := by
  simp [node_alloc, h]

theorem node_of_size_le (w : World) (k : Nat) (h : w.dom.size ≤ k) : w.node k = default := by
  simp [node_eq, Array.getElem?_eq_none h]

/-! ## Normal form: modifications of new nodes are absorbed into allocation -/

theorem ext_dom {w w' : World} (h : w.dom = w'.dom) (h1 : w.globals = w'.globals)
    (h2 : w.funcs = w'.funcs) (h3 : w.storage = w'.storage) (h4 : w.hash = w'.hash)
    (h5 : w.windowListeners = w'.windowListeners) : w = w' := by
  cases w; cases w'; simp_all

theorem alloc_modify_new (w : World) (nd : Node) (k : Nat) (f : Node → Node) (hk : k = w.dom.size) :
    (w.alloc nd).1.modify k f = (w.alloc (f nd)).1 := by
  subst hk
  refine ext_dom ?_ rfl rfl rfl rfl rfl
  apply Array.ext_getElem?
  intro i
  simp only [modify_dom, alloc_fst_dom, Array.getElem?_modify, Array.getElem?_push]
  by_cases h : w.dom.size = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem alloc_modify_old (w : World) (nd : Node) (k : Nat) (f : Node → Node) (hk : k < w.dom.size) :
    (w.alloc nd).1.modify k f = ((w.modify k f).alloc nd).1 := by
  refine ext_dom ?_ rfl rfl rfl rfl rfl
  apply Array.ext_getElem?
  intro i
  simp only [modify_dom, alloc_fst_dom, Array.getElem?_modify, Array.getElem?_push, Array.size_modify]
  by_cases h : i = w.dom.size
  · subst h; simp [Nat.ne_of_lt hk]
  · simp [h]

theorem modify_modify_same (w : World) (k : Nat) (f g : Node → Node) :
    (w.modify k f).modify k g = w.modify k (g ∘ f) := by
  refine ext_dom ?_ rfl rfl rfl rfl rfl
  apply Array.ext_getElem?
  intro i
  simp only [modify_dom, Array.getElem?_modify]
  by_cases h : k = i <;> simp [h]

/-! ## Tree operations -/

theorem detach_of_parent_none (w : World) (c : Nat) (h : (w.node c).parent = none) :
    w.detach c = w := by
  simp [World.detach, h]

/-- Appending a node which has no parent. -/
theorem appendChild_of_parent_none (w : World) (p c : Nat) (h : (w.node c).parent = none) :
    w.appendChild p c =
      (w.modify p fun nd => { nd with children := nd.children ++ [c] }).modify c
        fun nd => { nd with parent := some p } := by
  simp [World.appendChild, detach_of_parent_none w c h]

theorem replaceChildren_of_children_nil (w : World) (p : Nat) (h : (w.node p).children = []) :
    w.replaceChildren p = w.modify p fun nd => { nd with children := [] } := by
  simp [World.replaceChildren, h]

theorem setTextContent_eq (w : World) (n : Nat) (s : String) :
    w.setTextContent n s =
      if s = "" then w.replaceChildren n
      else ((w.replaceChildren n).alloc { tag := "#text", text := s }).1.appendChild n
        (w.replaceChildren n).dom.size := by
  unfold World.setTextContent
  by_cases h : s = "" <;> simp [h]

theorem size_foldl_modify (cs : List Nat) (f : Nat → Node → Node) :
    ∀ w : World, (cs.foldl (fun w c => w.modify c (f c)) w).dom.size = w.dom.size := by
  induction cs with
  | nil => intro; rfl
  | cons c cs ih => intro w; simp [ih]

@[simp] theorem size_replaceChildren (w : World) (p : Nat) :
    (w.replaceChildren p).dom.size = w.dom.size := by
  simp [World.replaceChildren, size_foldl_modify]

@[simp] theorem size_detach (w : World) (c : Nat) : (w.detach c).dom.size = w.dom.size := by
  unfold World.detach; split <;> simp

@[simp] theorem size_appendChild (w : World) (p c : Nat) :
    (w.appendChild p c).dom.size = w.dom.size := by
  simp [World.appendChild]

theorem size_setTextContent (w : World) (n : Nat) (s : String) :
    (w.setTextContent n s).dom.size = if s = "" then w.dom.size else w.dom.size + 1 := by
  rw [setTextContent_eq]
  split <;> simp

/-! ## Ancestor chains -/

/-- `Chain w n l`: following parent pointers from `n` visits exactly `l`. -/
inductive Chain (w : World) : Nat → List Nat → Prop
  | root {n} : (w.node n).parent = none → Chain w n [n]
  | step {n p l} : (w.node n).parent = some p → Chain w p l → Chain w n (n :: l)

theorem Chain.go_eq {w : World} {n l} (h : Chain w n l) :
    ∀ f, l.length ≤ f → ancestors.go w f n = l := by
  induction h with
  | root hp =>
    intro f hf
    rcases f with _ | f
    · simp at hf
    · simp [ancestors.go, hp]
  | step hp _ ih =>
    intro f hf
    rcases f with _ | f
    · simp at hf
    · simp only [List.length_cons, Nat.add_le_add_iff_right] at hf
      simp [ancestors.go, hp, ih f hf]

theorem Chain.ancestors_eq {w : World} {n l} (h : Chain w n l) (hl : l.length ≤ w.dom.size) :
    w.ancestors n = l := h.go_eq _ hl

/-- A chain only depends on the parent pointers along it. -/
theorem Chain.frame {w w' : World} {n l} (h : Chain w n l)
    (hp : ∀ m ∈ l, (w'.node m).parent = (w.node m).parent) : Chain w' n l := by
  induction h with
  | root h0 => exact .root ((hp _ (by simp)).trans h0)
  | step h0 _ ih =>
    exact .step ((hp _ (by simp)).trans h0) (ih fun m hm => hp m (by simp [hm]))

theorem ancestors_of_parent_none (w : World) (n : Nat) (h : (w.node n).parent = none)
    (hs : n < w.dom.size) : w.ancestors n = [n] := by
  apply (Chain.root h).ancestors_eq
  exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le n) hs)

theorem Chain.head_mem {w : World} {n l} (h : Chain w n l) : n ∈ l := by
  cases h <;> simp

theorem Chain.unique {w : World} {n l l'} (h : Chain w n l) (h' : Chain w n l') : l = l' := by
  induction h generalizing l' with
  | root hp =>
    cases h' with
    | root => rfl
    | step hp' _ => rw [hp] at hp'; cases hp'
  | step hp _ ih =>
    cases h' with
    | root hp' => rw [hp] at hp'; cases hp'
    | step hp' hc =>
      rw [hp] at hp'; cases hp'
      rw [ih hc]

theorem parent_foldl_none_of_not_mem (cs : List Nat) (k : Nat) (hk : k ∉ cs) :
    ∀ w : World, ((cs.foldl (fun w c => w.modify c fun nd => { nd with parent := none }) w).node k).parent =
      (w.node k).parent := by
  induction cs with
  | nil => intro; rfl
  | cons c cs ih =>
    intro w
    simp only [List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih hk.2, node_modify_ne _ _ _ _ (Ne.symm hk.1)]

theorem parent_replaceChildren_of_not_mem (w : World) (p k : Nat) (hk : k ∉ (w.node p).children) :
    ((w.replaceChildren p).node k).parent = (w.node k).parent := by
  unfold World.replaceChildren
  simp only
  rw [parent_modify_of]
  · exact parent_foldl_none_of_not_mem _ _ hk _
  · intro; rfl

theorem Chain.replaceChildren {w : World} {n p : Nat} {l : List Nat} (hc : Chain w n l)
    (hl : ∀ x ∈ l, x ∉ (w.node p).children) : Chain (w.replaceChildren p) n l :=
  hc.frame fun x hx => parent_replaceChildren_of_not_mem w p x (hl x hx)

theorem node_foldl_none (cs : List Nat) (k : Nat) :
    ∀ w : World, (cs.foldl (fun w c => w.modify c fun nd => { nd with parent := none }) w).node k =
      if k ∈ cs ∧ k < w.dom.size then { w.node k with parent := none } else w.node k := by
  induction cs with
  | nil => intro w; simp
  | cons c cs ih =>
    intro w
    rw [List.foldl_cons, ih, size_modify, node_modify]
    by_cases hc : c = k
    · subst hc; by_cases hs : c < w.dom.size <;> by_cases hm : c ∈ cs <;> simp [hs, hm]
    · simp only [hc, false_and, ite_false, List.mem_cons, Ne.symm hc, false_or]

theorem node_replaceChildren (w : World) (p k : Nat) :
    (w.replaceChildren p).node k =
      if k = p ∧ p < w.dom.size then
        { (if k ∈ (w.node p).children then { w.node k with parent := none } else w.node k) with children := [] }
      else if k ∈ (w.node p).children ∧ k < w.dom.size then { w.node k with parent := none }
      else w.node k := by
  unfold World.replaceChildren
  simp only
  rw [node_modify, size_foldl_modify, node_foldl_none]
  by_cases h1 : k = p
  · subst h1
    by_cases h2 : k < w.dom.size
    · by_cases h3 : k ∈ (w.node k).children <;> simp [h2, h3]
    · simp [h2]
  · simp [h1, Ne.symm h1]

/-! ## Parents have smaller indices than their children -/

/-- A parent always has a smaller index than its children. (A structure, so
that `simp` treats it as an atom.) -/
structure ParentLt (w : World) : Prop where
  lt : ∀ (k p : Nat), (w.node k).parent = some p → p < k

theorem ParentLt.go_le {w : World} (h : ParentLt w) :
    ∀ (f n x : Nat), x ∈ ancestors.go w f n → x ≤ n
  | 0, _, _, hx => by simp [ancestors.go] at hx
  | f + 1, n, x, hx => by
    simp only [ancestors.go, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_refl _
    · split at hx
      · rename_i q hq
        exact Nat.le_trans (ParentLt.go_le h f q x hx) (Nat.le_of_lt (h.lt n q hq))
      · simp at hx

theorem ParentLt.not_mem_ancestors {w : World} (h : ParentLt w) {p c : Nat} (hpc : p < c) :
    (w.ancestors p).contains c = false := by
  cases hc : (w.ancestors p).contains c
  · rfl
  · have := h.go_le _ _ _ (List.mem_of_elem_eq_true hc); omega

theorem parentLt_alloc {w : World} {nd : Node} (h : ParentLt w)
    (hn : ∀ p, nd.parent = some p → p < w.dom.size) : ParentLt (w.alloc nd).1 := by
  refine ⟨fun k p hk => ?_⟩
  rw [node_alloc] at hk
  split at hk
  · subst_vars; exact hn p hk
  · exact h.lt k p hk

theorem parentLt_modify_of {w : World} {n : Nat} {f : Node → Node} (h : ParentLt w)
    (hf : ∀ nd, (f nd).parent = nd.parent) : ParentLt (w.modify n f) := by
  refine ⟨fun k p hk => ?_⟩
  rw [parent_modify_of _ _ _ _ hf] at hk
  exact h.lt k p hk

theorem parentLt_modify_parent {w : World} {n p : Nat} {f : Node → Node} (h : ParentLt w)
    (hf : ∀ nd, (f nd).parent = some p) (hp : p < n) : ParentLt (w.modify n f) := by
  refine ⟨fun k q hk => ?_⟩
  rw [node_modify] at hk
  split at hk
  · rename_i hc; obtain ⟨rfl, -⟩ := hc; rw [hf] at hk; cases hk; exact hp
  · exact h.lt k q hk

theorem parentLt_foldl_none (cs : List Nat) :
    ∀ w : World, ParentLt w →
      ParentLt (cs.foldl (fun w c => w.modify c fun nd => { nd with parent := none }) w) := by
  induction cs with
  | nil => intro w h; exact h
  | cons c cs ih =>
    intro w h
    apply ih
    refine ⟨fun k p hk => ?_⟩
    rw [node_modify] at hk
    split at hk
    · simp at hk
    · exact h.lt k p hk

theorem parentLt_replaceChildren {w : World} {p : Nat} (h : ParentLt w) :
    ParentLt (w.replaceChildren p) := by
  unfold World.replaceChildren
  exact parentLt_modify_of (parentLt_foldl_none _ _ h) (fun _ => rfl)

theorem parentLt_modify_none {w : World} {n : Nat} (h : ParentLt w) :
    ParentLt (w.modify n fun nd => { nd with parent := none }) := by
  refine ⟨fun k q hk => ?_⟩
  rw [node_modify] at hk
  split at hk
  · simp at hk
  · exact h.lt k q hk

theorem parentLt_detach {w : World} {c : Nat} (h : ParentLt w) : ParentLt (w.detach c) := by
  unfold World.detach
  split
  · exact h
  · exact parentLt_modify_none (parentLt_modify_of h (fun _ => rfl))

theorem parentLt_appendChild {w : World} {p c : Nat} (h : ParentLt w) (hpc : p < c) :
    ParentLt (w.appendChild p c) := by
  unfold World.appendChild
  exact parentLt_modify_parent (parentLt_modify_of (parentLt_detach h) (fun _ => rfl)) (fun _ => rfl) hpc

theorem parentLt_setTextContent {w : World} {n : Nat} {s : String} (h : ParentLt w)
    (hn : n < w.dom.size) : ParentLt (w.setTextContent n s) := by
  rw [setTextContent_eq]
  split
  · exact parentLt_replaceChildren h
  · apply parentLt_appendChild _ (by simpa using hn)
    exact parentLt_alloc (parentLt_replaceChildren h) (by simp)

/-! ## Parent pointers agree with child lists -/

/-- Every node is in the child list of its parent. -/
structure ParentWF (w : World) : Prop where
  wf : ∀ (k p : Nat), (w.node k).parent = some p → k ∈ (w.node p).children

theorem lt_size_of_parent {w : World} {k p : Nat} (hk : (w.node k).parent = some p) : k < w.dom.size := by
  by_cases hc : k < w.dom.size
  · exact hc
  · rw [node_of_size_le w k (by omega)] at hk; cases hk

theorem parentWF_alloc {w : World} {nd : Node} (h : ParentWF w) (hl : ParentLt w)
    (hn : ∀ p, nd.parent = some p → w.dom.size ∈ (w.node p).children) : ParentWF (w.alloc nd).1 := by
  refine ⟨fun k p hk => ?_⟩
  rw [node_alloc] at hk
  split at hk
  · subst_vars
    have hp := hn p hk
    have hps : p < w.dom.size := by
      by_cases hc : p < w.dom.size
      · exact hc
      · rw [node_of_size_le w p (by omega)] at hp; exact (List.not_mem_nil hp).elim
    rw [node_alloc_old _ _ _ (by omega)]
    exact hp
  · have hks := lt_size_of_parent hk
    have hpk := hl.lt k p hk
    rw [node_alloc_old _ _ _ (by omega)]
    exact h.wf k p hk

theorem parentWF_modify_of {w : World} {n : Nat} {f : Node → Node} (h : ParentWF w)
    (hp : ∀ nd, (f nd).parent = nd.parent) (hc : ∀ nd, ∀ x ∈ nd.children, x ∈ (f nd).children) :
    ParentWF (w.modify n f) := by
  refine ⟨fun k p hk => ?_⟩
  rw [parent_modify_of _ _ _ _ hp] at hk
  have := h.wf k p hk
  rw [node_modify]
  split
  · rename_i hc'; obtain ⟨rfl, -⟩ := hc'; exact hc _ _ this
  · exact this

theorem parentWF_modify_parent {w : World} {c p : Nat} (h : ParentWF w)
    (hc : c ∈ (w.node p).children) : ParentWF (w.modify c fun nd => { nd with parent := some p }) := by
  refine ⟨fun k q hk => ?_⟩
  rw [children_modify_of (f := fun nd => { nd with parent := some p }) _ _ _ (fun _ => rfl)]
  rw [node_modify] at hk
  split at hk
  · rename_i hk'; obtain ⟨rfl, -⟩ := hk'; cases hk; exact hc
  · exact h.wf k q hk

theorem parentWF_foldl_none (cs : List Nat) :
    ∀ w : World, ParentWF w →
      ParentWF (cs.foldl (fun w c => w.modify c fun nd => { nd with parent := none }) w) := by
  induction cs with
  | nil => intro w h; exact h
  | cons c cs ih =>
    intro w h
    apply ih
    refine ⟨fun k q hk => ?_⟩
    rw [children_modify_of (f := fun nd => { nd with parent := none }) _ _ _ (fun _ => rfl)]
    rw [node_modify] at hk
    split at hk
    · cases hk
    · exact h.wf k q hk

theorem children_replaceChildren_ne (w : World) (p q : Nat) (hq : q ≠ p) :
    ((w.replaceChildren p).node q).children = (w.node q).children := by
  rw [node_replaceChildren]
  simp only [hq, false_and, ite_false]
  split <;> rfl

theorem parentWF_replaceChildren {w : World} {p : Nat} (h : ParentWF w) :
    ParentWF (w.replaceChildren p) := by
  refine ⟨fun k q hk => ?_⟩
  have hks : k < w.dom.size := by
    have := lt_size_of_parent hk; simpa using this
  rw [node_replaceChildren] at hk
  by_cases hkp : k = p ∧ p < w.dom.size
  · obtain ⟨rfl, hs⟩ := hkp
    simp only [hs, and_self, ite_true] at hk
    split at hk
    · cases hk
    · rename_i hm
      have hw := h.wf k q hk
      have hqk : q ≠ k := fun e => by subst e; exact hm hw
      rw [children_replaceChildren_ne _ _ _ hqk]; exact hw
  · simp only [hkp, ite_false] at hk
    split at hk
    · cases hk
    · rename_i hm
      have hw := h.wf k q hk
      by_cases hqp : q = p
      · subst hqp; exact absurd ⟨hw, hks⟩ hm
      · rw [children_replaceChildren_ne _ _ _ hqp]; exact hw

theorem parentWF_detach {w : World} {c : Nat} (h : ParentWF w) : ParentWF (w.detach c) := by
  unfold World.detach
  split
  · exact h
  · rename_i q hq
    refine ⟨fun k p hk => ?_⟩
    rw [node_modify] at hk
    split at hk
    · cases hk
    · rename_i hkc
      rw [parent_modify_of (f := fun nd => { nd with children := nd.children.filter (· != c) }) _ _ _
        (fun _ => rfl)] at hk
      rw [children_modify_of (f := fun nd => { nd with parent := none }) _ _ _ (fun _ => rfl), node_modify]
      have hw := h.wf k p hk
      have hck : c ≠ k := by
        intro e; subst e; exact hkc ⟨rfl, by simpa using lt_size_of_parent hk⟩
      split
      · rename_i he; obtain ⟨rfl, -⟩ := he
        simp only [List.mem_filter, bne_iff_ne, ne_eq]
        exact ⟨hw, fun e => hck e.symm⟩
      · exact hw

theorem parentWF_appendChild {w : World} {p c : Nat} (h : ParentWF w) (hc : c < w.dom.size)
    (hp : p < w.dom.size) : ParentWF (w.appendChild p c) := by
  unfold World.appendChild
  apply parentWF_modify_parent
  · exact parentWF_modify_of (parentWF_detach h) (fun _ => rfl) (fun nd x hx => by simp [hx])
  · rw [node_modify_self _ _ _ (by simpa using hp)]
    simp

theorem parentWF_setTextContent {w : World} {n : Nat} {s : String} (h : ParentWF w) (hl : ParentLt w)
    (hn : n < w.dom.size) : ParentWF (w.setTextContent n s) := by
  rw [setTextContent_eq]
  split
  · exact parentWF_replaceChildren h
  · apply parentWF_appendChild _ (by simp) (by simpa using Nat.lt_succ_of_lt hn)
    exact parentWF_alloc (parentWF_replaceChildren h) (parentLt_replaceChildren hl) (by simp)

/-! ## The setters do not affect the DOM properties -/

theorem chain_congr {w w' : World} (h : ∀ k, w'.node k = w.node k) {n : Nat} {l : List Nat} :
    Chain w' n l ↔ Chain w n l :=
  ⟨fun hc => hc.frame fun x _ => by rw [h], fun hc => hc.frame fun x _ => by rw [h]⟩

@[simp] theorem chain_setGlobals (w : World) g n l : Chain (w.setGlobals g) n l ↔ Chain w n l :=
  chain_congr (w := w) (w' := w.setGlobals g) (fun _ => rfl)
@[simp] theorem chain_setStorage (w : World) st n l : Chain (w.setStorage st) n l ↔ Chain w n l :=
  chain_congr (w := w) (w' := w.setStorage st) (fun _ => rfl)
@[simp] theorem chain_setHash (w : World) h n l : Chain (w.setHash h) n l ↔ Chain w n l :=
  chain_congr (w := w) (w' := w.setHash h) (fun _ => rfl)
@[simp] theorem parentLt_setGlobals (w : World) g : ParentLt (w.setGlobals g) ↔ ParentLt w :=
  ⟨fun h => ⟨h.lt⟩, fun h => ⟨h.lt⟩⟩
@[simp] theorem parentLt_setStorage (w : World) st : ParentLt (w.setStorage st) ↔ ParentLt w :=
  ⟨fun h => ⟨h.lt⟩, fun h => ⟨h.lt⟩⟩
@[simp] theorem parentLt_setHash (w : World) h : ParentLt (w.setHash h) ↔ ParentLt w :=
  ⟨fun h => ⟨h.lt⟩, fun h => ⟨h.lt⟩⟩
@[simp] theorem parentWF_setGlobals (w : World) g : ParentWF (w.setGlobals g) ↔ ParentWF w :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩
@[simp] theorem parentWF_setStorage (w : World) st : ParentWF (w.setStorage st) ↔ ParentWF w :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩
@[simp] theorem parentWF_setHash (w : World) h : ParentWF (w.setHash h) ↔ ParentWF w :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

@[simp] theorem setGlobals_setGlobals (w : World) g g' : (w.setGlobals g).setGlobals g' = w.setGlobals g' := rfl
@[simp] theorem setStorage_setStorage (w : World) st st' :
    (w.setStorage st).setStorage st' = w.setStorage st' := rfl
theorem modify_setGlobals (w : World) g n f : (w.setGlobals g).modify n f = (w.modify n f).setGlobals g := rfl
theorem modify_setStorage (w : World) st n f : (w.setStorage st).modify n f = (w.modify n f).setStorage st := rfl
theorem setGlobals_setStorage (w : World) g st : (w.setStorage st).setGlobals g = (w.setGlobals g).setStorage st := rfl

theorem chain_modify_iff {w : World} {n : Nat} {f : Node → Node} (hf : ∀ nd, (f nd).parent = nd.parent)
    (k : Nat) (l : List Nat) : Chain (w.modify n f) k l ↔ Chain w k l :=
  ⟨fun hc => hc.frame fun x _ => (parent_modify_of _ _ _ _ hf).symm,
   fun hc => hc.frame fun x _ => parent_modify_of _ _ _ _ hf⟩

end World
