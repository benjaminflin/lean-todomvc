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

theorem SameButDom.foldl_modify (cs : List NodeId) (f : NodeId → Node → Node) :
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

@[simp] theorem detach_globals (w : World) (c : NodeId) : (w.detach c).globals = w.globals :=
  (SameButDom.detach w c).globals
@[simp] theorem detach_funcs (w : World) (c : NodeId) : (w.detach c).funcs = w.funcs :=
  (SameButDom.detach w c).funcs
@[simp] theorem detach_storage (w : World) (c : NodeId) : (w.detach c).storage = w.storage :=
  (SameButDom.detach w c).storage
@[simp] theorem detach_hash (w : World) (c : NodeId) : (w.detach c).hash = w.hash :=
  (SameButDom.detach w c).hash
@[simp] theorem detach_windowListeners (w : World) (c : NodeId) : (w.detach c).windowListeners = w.windowListeners :=
  (SameButDom.detach w c).windowListeners
@[simp] theorem appendChild_globals (w : World) (p c : NodeId) : (w.appendChild p c).globals = w.globals :=
  (SameButDom.appendChild w p c).globals
@[simp] theorem appendChild_funcs (w : World) (p c : NodeId) : (w.appendChild p c).funcs = w.funcs :=
  (SameButDom.appendChild w p c).funcs
@[simp] theorem appendChild_storage (w : World) (p c : NodeId) : (w.appendChild p c).storage = w.storage :=
  (SameButDom.appendChild w p c).storage
@[simp] theorem appendChild_hash (w : World) (p c : NodeId) : (w.appendChild p c).hash = w.hash :=
  (SameButDom.appendChild w p c).hash
@[simp] theorem appendChild_windowListeners (w : World) (p c : NodeId) : (w.appendChild p c).windowListeners = w.windowListeners :=
  (SameButDom.appendChild w p c).windowListeners
@[simp] theorem replaceChildren_globals (w : World) (p : NodeId) : (w.replaceChildren p).globals = w.globals :=
  (SameButDom.replaceChildren w p).globals
@[simp] theorem replaceChildren_funcs (w : World) (p : NodeId) : (w.replaceChildren p).funcs = w.funcs :=
  (SameButDom.replaceChildren w p).funcs
@[simp] theorem replaceChildren_storage (w : World) (p : NodeId) : (w.replaceChildren p).storage = w.storage :=
  (SameButDom.replaceChildren w p).storage
@[simp] theorem replaceChildren_hash (w : World) (p : NodeId) : (w.replaceChildren p).hash = w.hash :=
  (SameButDom.replaceChildren w p).hash
@[simp] theorem replaceChildren_windowListeners (w : World) (p : NodeId) : (w.replaceChildren p).windowListeners = w.windowListeners :=
  (SameButDom.replaceChildren w p).windowListeners
@[simp] theorem setTextContent_globals (w : World) (n : NodeId) (t : String) : (w.setTextContent n t).globals = w.globals :=
  (SameButDom.setTextContent w n t).globals
@[simp] theorem setTextContent_funcs (w : World) (n : NodeId) (t : String) : (w.setTextContent n t).funcs = w.funcs :=
  (SameButDom.setTextContent w n t).funcs
@[simp] theorem setTextContent_storage (w : World) (n : NodeId) (t : String) : (w.setTextContent n t).storage = w.storage :=
  (SameButDom.setTextContent w n t).storage
@[simp] theorem setTextContent_hash (w : World) (n : NodeId) (t : String) : (w.setTextContent n t).hash = w.hash :=
  (SameButDom.setTextContent w n t).hash
@[simp] theorem setTextContent_windowListeners (w : World) (n : NodeId) (t : String) : (w.setTextContent n t).windowListeners = w.windowListeners :=
  (SameButDom.setTextContent w n t).windowListeners

/-! ## Nodes -/

@[simp] theorem size_modify (w : World) n f : (w.modify n f).dom.size = w.dom.size := Array.size_modify

theorem node_eq (w : World) (k : NodeId) : w.node k = (w.dom[k]?).getD default := rfl

theorem node_modify (w : World) (n : NodeId) (f : Node → Node) (k : NodeId) :
    (w.modify n f).node k = if n = k ∧ k < w.dom.size then f (w.node k) else w.node k := by
  simp only [node_eq, modify_dom, Array.getElem?_modify]
  by_cases h : n = k
  · subst h
    by_cases hk : n < w.dom.size
    · simp [hk, Array.getElem?_eq_getElem hk]
    · simp [hk, Array.getElem?_eq_none (Nat.le_of_not_lt hk)]
  · simp [h]

@[simp] theorem node_modify_self (w : World) (n : NodeId) (f : Node → Node) (h : n < w.dom.size) :
    (w.modify n f).node n = f (w.node n) := by
  simp [node_modify, h]

@[simp] theorem node_modify_ne (w : World) (n k : NodeId) (f : Node → Node) (h : n ≠ k) :
    (w.modify n f).node k = w.node k := by
  simp [node_modify, h]

theorem parent_modify_of (w : World) (n : NodeId) (f : Node → Node) (k : NodeId)
    (hf : ∀ nd, (f nd).parent = nd.parent) : ((w.modify n f).node k).parent = (w.node k).parent := by
  rw [node_modify]; split <;> simp [hf]

theorem children_modify_of (w : World) (n : NodeId) (f : Node → Node) (k : NodeId)
    (hf : ∀ nd, (f nd).children = nd.children) :
    ((w.modify n f).node k).children = (w.node k).children := by
  rw [node_modify]; split <;> simp [hf]

theorem node_alloc (w : World) (nd : Node) (k : NodeId) :
    (w.alloc nd).1.node k = if k = w.dom.size then nd else w.node k := by
  simp only [node_eq, alloc_fst_dom, Array.getElem?_push]
  split <;> simp

@[simp] theorem node_alloc_new (w : World) (nd : Node) : (w.alloc nd).1.node w.dom.size = nd := by
  simp [node_alloc]

theorem node_alloc_eq (w : World) (nd : Node) (k : NodeId) (h : k = w.dom.size) :
    (w.alloc nd).1.node k = nd := by
  subst h; simp [node_alloc]

@[simp] theorem node_alloc_old (w : World) (nd : Node) (k : NodeId) (h : k ≠ w.dom.size) :
    (w.alloc nd).1.node k = w.node k := by
  simp [node_alloc, h]

theorem node_of_size_le (w : World) (k : NodeId) (h : w.dom.size ≤ k) : w.node k = default := by
  simp [node_eq, Array.getElem?_eq_none h]

/-! ## Normal form: modifications of new nodes are absorbed into allocation -/

theorem ext_dom {w w' : World} (h : w.dom = w'.dom) (h1 : w.globals = w'.globals)
    (h2 : w.funcs = w'.funcs) (h3 : w.storage = w'.storage) (h4 : w.hash = w'.hash)
    (h5 : w.windowListeners = w'.windowListeners) : w = w' := by
  cases w; cases w'; simp_all

theorem alloc_modify_new (w : World) (nd : Node) (k : NodeId) (f : Node → Node) (hk : k = w.dom.size) :
    (w.alloc nd).1.modify k f = (w.alloc (f nd)).1 := by
  subst hk
  refine ext_dom ?_ rfl rfl rfl rfl rfl
  apply Array.ext_getElem?
  intro i
  simp only [modify_dom, alloc_fst_dom, Array.getElem?_modify, Array.getElem?_push]
  by_cases h : w.dom.size = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem alloc_modify_old (w : World) (nd : Node) (k : NodeId) (f : Node → Node) (hk : k < w.dom.size) :
    (w.alloc nd).1.modify k f = ((w.modify k f).alloc nd).1 := by
  refine ext_dom ?_ rfl rfl rfl rfl rfl
  apply Array.ext_getElem?
  intro i
  simp only [modify_dom, alloc_fst_dom, Array.getElem?_modify, Array.getElem?_push, Array.size_modify]
  by_cases h : i = w.dom.size
  · subst h; simp [Nat.ne_of_lt hk]
  · simp [h]

theorem modify_modify_same (w : World) (k : NodeId) (f g : Node → Node) :
    (w.modify k f).modify k g = w.modify k (g ∘ f) := by
  refine ext_dom ?_ rfl rfl rfl rfl rfl
  apply Array.ext_getElem?
  intro i
  simp only [modify_dom, Array.getElem?_modify]
  by_cases h : k = i <;> simp [h]

/-! ## Tree operations -/

theorem detach_of_parent_none (w : World) (c : NodeId) (h : (w.node c).parent = none) :
    w.detach c = w := by
  simp [World.detach, h]

/-- Appending a node which has no parent. -/
theorem appendChild_of_parent_none (w : World) (p c : NodeId) (h : (w.node c).parent = none) :
    w.appendChild p c =
      (w.modify p fun nd => { nd with children := nd.children ++ [c] }).modify c
        fun nd => { nd with parent := some p } := by
  simp [World.appendChild, detach_of_parent_none w c h]

theorem replaceChildren_of_children_nil (w : World) (p : NodeId) (h : (w.node p).children = []) :
    w.replaceChildren p = w.modify p fun nd => { nd with children := [] } := by
  simp [World.replaceChildren, h]

theorem setTextContent_eq (w : World) (n : NodeId) (s : String) :
    w.setTextContent n s =
      if s = "" then w.replaceChildren n
      else ((w.replaceChildren n).alloc { tag := "#text", text := s }).1.appendChild n
        (w.replaceChildren n).dom.size := by
  unfold World.setTextContent
  by_cases h : s = "" <;> simp [h]

theorem size_foldl_modify (cs : List NodeId) (f : NodeId → Node → Node) :
    ∀ w : World, (cs.foldl (fun w c => w.modify c (f c)) w).dom.size = w.dom.size := by
  induction cs with
  | nil => intro; rfl
  | cons c cs ih => intro w; simp [ih]

@[simp] theorem size_replaceChildren (w : World) (p : NodeId) :
    (w.replaceChildren p).dom.size = w.dom.size := by
  simp [World.replaceChildren, size_foldl_modify]

@[simp] theorem size_detach (w : World) (c : NodeId) : (w.detach c).dom.size = w.dom.size := by
  unfold World.detach; split <;> simp

@[simp] theorem size_appendChild (w : World) (p c : NodeId) :
    (w.appendChild p c).dom.size = w.dom.size := by
  simp [World.appendChild]

/-! ## Ancestor chains -/

/-- `Chain w n l`: following parent pointers from `n` visits exactly `l`. -/
inductive Chain (w : World) : NodeId → List NodeId → Prop
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

theorem ancestors_of_parent_none (w : World) (n : NodeId) (h : (w.node n).parent = none)
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

end World
