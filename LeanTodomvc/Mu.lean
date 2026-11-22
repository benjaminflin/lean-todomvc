import Mathlib.Order.FixedPoints
import Mathlib.Logic.Relation

/-!
# The modal μ-calculus over a deterministic labelled transition system

Formulas are in positive normal form, with de Bruijn indices for fixpoint
variables. Atomic propositions are arbitrary predicates on states, so negation
is only needed on atoms, where it is just another predicate. Without negation
every formula is monotone in its variables, so `μ`/`ν` are well defined.

Modalities are indexed by a *state-dependent* set of actions, so we can say
e.g. "after any click on a visible `.destroy` button": `[P] φ` holds at `s`
if `φ` holds after every action `a` with `P s a`.

The semantics is relative to a transition function `δ : S → A → S`.
-/

namespace Mu

inductive Formula (S A : Type) where
  | tt
  | ff
  | atom (p : S → Prop)
  | and (φ ψ : Formula S A)
  | or (φ ψ : Formula S A)
  /-- `⟨P⟩φ`: some action `a` with `P s a` leads to a state satisfying `φ` -/
  | dia (P : S → A → Prop) (φ : Formula S A)
  /-- `[P]φ`: every action `a` with `P s a` leads to a state satisfying `φ` -/
  | box (P : S → A → Prop) (φ : Formula S A)
  | var (i : Nat)
  | mu (φ : Formula S A)
  | nu (φ : Formula S A)

variable {S A : Type}

abbrev Env (S : Type) := Nat → Set S

def Env.cons (X : Set S) (ρ : Env S) : Env S
  | 0 => X
  | n + 1 => ρ n

/-- Insert `X` at position `k`, shifting the variables `≥ k` up by one. -/
def Env.insertAt (k : Nat) (X : Set S) (ρ : Env S) : Env S := fun i =>
  if i < k then ρ i else if i = k then X else ρ (i - 1)

variable (δ : S → A → S)

def sem : Formula S A → Env S → Set S
  | .tt, _ => Set.univ
  | .ff, _ => ∅
  | .atom p, _ => {s | p s}
  | .and φ ψ, ρ => sem φ ρ ∩ sem ψ ρ
  | .or φ ψ, ρ => sem φ ρ ∪ sem ψ ρ
  | .dia P φ, ρ => {s | ∃ a, P s a ∧ δ s a ∈ sem φ ρ}
  | .box P φ, ρ => {s | ∀ a, P s a → δ s a ∈ sem φ ρ}
  | .var i, ρ => ρ i
  | .mu φ, ρ => sInf {X | sem φ (ρ.cons X) ≤ X}
  | .nu φ, ρ => sSup {X | X ≤ sem φ (ρ.cons X)}

theorem sem_mono (φ : Formula S A) : ∀ {ρ ρ' : Env S}, ρ ≤ ρ' → sem δ φ ρ ≤ sem δ φ ρ' := by
  induction φ with
  | tt | ff | atom => intros; exact le_rfl
  | and φ ψ ihφ ihψ => intro _ _ h; exact Set.inter_subset_inter (ihφ h) (ihψ h)
  | or φ ψ ihφ ihψ => intro _ _ h; exact Set.union_subset_union (ihφ h) (ihψ h)
  | dia P φ ih => intro _ _ h s ⟨a, hP, ha⟩; exact ⟨a, hP, ih h ha⟩
  | box P φ ih => intro _ _ h s hs a hP; exact ih h (hs a hP)
  | var i => intro _ _ h; exact h i
  | mu φ ih =>
    intro ρ ρ' h
    apply sInf_le_sInf
    intro X hX
    exact le_trans (ih (ρ := ρ.cons X) (ρ' := ρ'.cons X) (fun | 0 => le_rfl | n + 1 => h n)) hX
  | nu φ ih =>
    intro ρ ρ' h
    apply sSup_le_sSup
    intro X hX
    exact le_trans hX (ih (ρ := ρ.cons X) (ρ' := ρ'.cons X) (fun | 0 => le_rfl | n + 1 => h n))

/-- The body of a fixpoint formula as a monotone function. -/
def body (φ : Formula S A) (ρ : Env S) : Set S →o Set S where
  toFun X := sem δ φ (ρ.cons X)
  monotone' _ _ h := sem_mono δ φ (fun | 0 => h | _ + 1 => le_rfl)

theorem sem_mu (φ : Formula S A) (ρ : Env S) : sem δ (.mu φ) ρ = OrderHom.lfp (body δ φ ρ) := rfl
theorem sem_nu (φ : Formula S A) (ρ : Env S) : sem δ (.nu φ) ρ = OrderHom.gfp (body δ φ ρ) := rfl

/-! ## Shifting de Bruijn indices -/

/-- Shift the free variables `≥ k` up by one. -/
def Formula.liftAt (k : Nat) : Formula S A → Formula S A
  | .and φ ψ => .and (φ.liftAt k) (ψ.liftAt k)
  | .or φ ψ => .or (φ.liftAt k) (ψ.liftAt k)
  | .dia P φ => .dia P (φ.liftAt k)
  | .box P φ => .box P (φ.liftAt k)
  | .var i => if i < k then .var i else .var (i + 1)
  | .mu φ => .mu (φ.liftAt (k + 1))
  | .nu φ => .nu (φ.liftAt (k + 1))
  | φ => φ

abbrev Formula.lift (φ : Formula S A) : Formula S A := φ.liftAt 0

theorem Env.cons_insertAt (k : Nat) (X Y : Set S) (ρ : Env S) :
    (Env.insertAt k X ρ).cons Y = Env.insertAt (k + 1) X (ρ.cons Y) := by
  funext i
  rcases i with _ | i
  · simp [Env.cons, Env.insertAt]
  · simp only [Env.cons, Env.insertAt, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    split_ifs with h1 h2 <;> try rfl
    rcases i with _ | i
    · omega
    · rfl

theorem sem_liftAt (φ : Formula S A) :
    ∀ (k : Nat) (X : Set S) (ρ : Env S), sem δ (φ.liftAt k) (Env.insertAt k X ρ) = sem δ φ ρ := by
  induction φ with
  | tt | ff | atom => intros; rfl
  | and φ ψ ihφ ihψ => intros; simp only [Formula.liftAt, sem, ihφ, ihψ]
  | or φ ψ ihφ ihψ => intros; simp only [Formula.liftAt, sem, ihφ, ihψ]
  | dia P φ ih => intros; simp only [Formula.liftAt, sem, ih]
  | box P φ ih => intros; simp only [Formula.liftAt, sem, ih]
  | var i =>
    intro k X ρ
    simp only [Formula.liftAt]
    split_ifs with h
    · simp [sem, Env.insertAt, h]
    · have h1 : ¬ i + 1 < k := by omega
      have h2 : ¬ i + 1 = k := by omega
      simp [sem, Env.insertAt, h1, h2]
  | mu φ ih => intros; simp only [Formula.liftAt, sem, Env.cons_insertAt, ih]
  | nu φ ih => intros; simp only [Formula.liftAt, sem, Env.cons_insertAt, ih]

theorem sem_lift (φ : Formula S A) (X : Set S) (ρ : Env S) :
    sem δ φ.lift (ρ.cons X) = sem δ φ ρ := by
  have : ρ.cons X = Env.insertAt 0 X ρ := by
    funext i; rcases i with _ | i <;> simp [Env.cons, Env.insertAt]
  rw [this, sem_liftAt]

/-! ## Derived operators (CTL-style) -/

/-- Every action. -/
def anyAct : S → A → Prop := fun _ _ => True

namespace Formula

/-- `AX φ` -/
def AX (φ : Formula S A) : Formula S A := .box anyAct φ
/-- `EX φ` -/
def EX (φ : Formula S A) : Formula S A := .dia anyAct φ
/-- `AG φ = νX. φ ∧ [·]X`: `φ` holds in every reachable state. -/
def AG (φ : Formula S A) : Formula S A := .nu (.and φ.lift (.box anyAct (.var 0)))
/-- `EF φ = μX. φ ∨ ⟨·⟩X`: some reachable state satisfies `φ`. -/
def EF (φ : Formula S A) : Formula S A := .mu (.or φ.lift (.dia anyAct (.var 0)))
/-- `E[φ U ψ] = μX. ψ ∨ (φ ∧ ⟨·⟩X)` -/
def EU (φ ψ : Formula S A) : Formula S A := .mu (.or ψ.lift (.and φ.lift (.dia anyAct (.var 0))))

end Formula

/-! ## Reachability characterisations -/

/-- One step of the transition system, by any action. -/
def Step (s t : S) : Prop := ∃ a, δ s a = t

abbrev Reachable : S → S → Prop := Relation.ReflTransGen (Step δ)

theorem mem_AG (φ : Formula S A) (ρ : Env S) (s : S) :
    s ∈ sem δ φ.AG ρ ↔ ∀ t, Reachable δ s t → t ∈ sem δ φ ρ := by
  have unfold : ∀ X, body δ (.and φ.lift (.box anyAct (.var 0))) ρ X =
      sem δ φ ρ ∩ {s | ∀ a, δ s a ∈ X} := by
    intro X; ext s; simp [body, sem, sem_lift, Env.cons, anyAct]
  constructor
  · intro hs t hr
    have post : ∀ u ∈ sem δ φ.AG ρ, u ∈ sem δ φ ρ ∧ ∀ a, δ u a ∈ sem δ φ.AG ρ := by
      intro u hu
      rw [Formula.AG, sem_nu, ← OrderHom.map_gfp, unfold] at hu
      exact hu
    have reach : ∀ t, Reachable δ s t → t ∈ sem δ φ.AG ρ := by
      intro t hr
      induction hr with
      | refl => exact hs
      | tail _ hst ih =>
        obtain ⟨a, rfl⟩ := hst
        exact (post _ ih).2 a
    exact (post t (reach t hr)).1
  · intro hs
    rw [Formula.AG, sem_nu]
    let R : Set S := {u | ∀ t, Reachable δ u t → t ∈ sem δ φ ρ}
    have hR : R ≤ body δ (.and φ.lift (.box anyAct (.var 0))) ρ R := by
      intro u hu
      rw [unfold]
      exact ⟨hu u .refl, fun a t ht => hu t (.head ⟨a, rfl⟩ ht)⟩
    exact OrderHom.le_gfp _ hR hs

theorem mem_EF (φ : Formula S A) (ρ : Env S) (s : S) :
    s ∈ sem δ φ.EF ρ ↔ ∃ t, Reachable δ s t ∧ t ∈ sem δ φ ρ := by
  have unfold : ∀ X, body δ (.or φ.lift (.dia anyAct (.var 0))) ρ X =
      sem δ φ ρ ∪ {s | ∃ a, δ s a ∈ X} := by
    intro X; ext s; simp [body, sem, sem_lift, Env.cons, anyAct]
  constructor
  · intro hs
    rw [Formula.EF, sem_mu] at hs
    let R : Set S := {u | ∃ t, Reachable δ u t ∧ t ∈ sem δ φ ρ}
    have hR : body δ (.or φ.lift (.dia anyAct (.var 0))) ρ R ≤ R := by
      rw [unfold]
      rintro u (hu | ⟨a, t, hr, ht⟩)
      · exact ⟨u, .refl, hu⟩
      · exact ⟨t, .head ⟨a, rfl⟩ hr, ht⟩
    exact OrderHom.lfp_le _ hR hs
  · rintro ⟨t, hr, ht⟩
    have fix : sem δ φ.EF ρ = sem δ φ ρ ∪ {s | ∃ a, δ s a ∈ sem δ φ.EF ρ} := by
      rw [Formula.EF, sem_mu, ← unfold, OrderHom.map_lfp]
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => rw [fix]; exact Or.inl ht
    | head hst _ ih =>
      obtain ⟨a, rfl⟩ := hst
      rw [fix]; exact Or.inr ⟨a, ih⟩

/-! ## Modalities for a deterministic system -/

@[simp] theorem mem_dia (P : S → A → Prop) (φ : Formula S A) (ρ : Env S) (s : S) :
    s ∈ sem δ (.dia P φ) ρ ↔ ∃ a, P s a ∧ δ s a ∈ sem δ φ ρ := Iff.rfl

@[simp] theorem mem_box (P : S → A → Prop) (φ : Formula S A) (ρ : Env S) (s : S) :
    s ∈ sem δ (.box P φ) ρ ↔ ∀ a, P s a → δ s a ∈ sem δ φ ρ := Iff.rfl

@[simp] theorem mem_atom (p : S → Prop) (ρ : Env S) (s : S) :
    s ∈ sem δ (.atom p : Formula S A) ρ ↔ p s := Iff.rfl

@[simp] theorem mem_and (φ ψ : Formula S A) (ρ : Env S) (s : S) :
    s ∈ sem δ (.and φ ψ) ρ ↔ s ∈ sem δ φ ρ ∧ s ∈ sem δ ψ ρ := Iff.rfl

@[simp] theorem mem_or (φ ψ : Formula S A) (ρ : Env S) (s : S) :
    s ∈ sem δ (.or φ ψ) ρ ↔ s ∈ sem δ φ ρ ∨ s ∈ sem δ ψ ρ := Iff.rfl

/-- `⟨a⟩φ` for a single action. -/
def Formula.after (a : A) (φ : Formula S A) : Formula S A := .dia (fun _ b => b = a) φ

@[simp] theorem mem_after (a : A) (φ : Formula S A) (ρ : Env S) (s : S) :
    s ∈ sem δ (φ.after a) ρ ↔ δ s a ∈ sem δ φ ρ := by
  simp [Formula.after]

/-! ## Bounded checking

`AGn k P φ` says that `φ` holds along every path of at most `k` actions drawn
from `P`. When `P` is a finite set of actions for each state, this can be
decided by exhaustive search (`checkAGn`), which is proved sound. This is a
bounded under-approximation of `AG`.
-/

def Formula.AGn (P : S → A → Prop) (φ : Formula S A) : Nat → Formula S A
  | 0 => φ
  | k + 1 => .and φ (.box P (Formula.AGn P φ k))

def checkAGn (gen : S → List A) (p : S → Bool) : Nat → S → Bool
  | 0, s => p s
  | k + 1, s => p s && (gen s).all fun a => checkAGn gen p k (δ s a)

theorem checkAGn_sound (gen : S → List A) (p : S → Bool) (ρ : Env S) :
    ∀ k s, checkAGn δ gen p k s = true →
      s ∈ sem δ ((Formula.atom (fun s => p s = true)).AGn (fun s a => a ∈ gen s) k) ρ := by
  intro k
  induction k with
  | zero => intro s h; exact h
  | succ k ih =>
    intro s h
    simp only [checkAGn, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨h.1, fun a ha => ih _ (h.2 a ha)⟩

/-- `M, s ⊨ φ` for closed `φ`. -/
def Sat (s : S) (φ : Formula S A) : Prop := s ∈ sem δ φ (fun _ => ∅)

end Mu
