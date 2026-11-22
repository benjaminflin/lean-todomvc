import LeanTodomvc.Proof.Step

/-!
# The nodes in the document

In a represented state, every node in the document is a static node, a node of
a rendered todo item, or a node of the counter.
-/

namespace TodoMVC.Proof
open JS DOM
open World (ParentWF ParentLt Chain)

theorem blockNode_children_mem (b : Nat) (t : TodoR) (ed : Bool) (par : Option Nat) (v2 ve : String)
    (i x : Nat) (hx : x ∈ (blockNode b t ed par v2 ve i).children) : b < x ∧ x < b + blockSize t ed := by
  unfold blockNode at hx
  split at hx
  · simp at hx; rcases hx with rfl | ⟨he, rfl⟩ <;> simp [blockSize, dOff] <;> split <;> simp_all <;> omega
  · simp at hx; rcases hx with rfl | rfl | rfl <;> simp [blockSize, dOff] <;> split <;> omega
  · cases hx
  · split at hx <;> simp at hx; obtain ⟨-, rfl⟩ := hx; simp [blockSize, dOff, *]; omega
  · split_ifs at hx <;> first | cases hx | (rw [show (default : Node).children = [] from rfl] at hx; cases hx)

theorem forall₂_zip {α β} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a b, (a, b) ∈ l₁.zip l₂ → R a b
  | _, _, .nil => by simp
  | _, _, .cons hab hr => by
    intro a b h
    rcases List.mem_cons.1 h with h | h
    · cases h; exact hab
    · exact forall₂_zip hr a b h

theorem forall₂_mem_zip {α β} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, (a, b) ∈ l₁.zip l₂
  | _, _, .nil => by simp
  | _, _, .cons (a := a₀) (b := b₀) _ hr => by
    intro a h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨b₀, by simp⟩
    · obtain ⟨b, hb⟩ := forall₂_mem_zip hr a h
      exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-- A node is static, in the counter, or in the block of a shown todo. -/
def Known (m : Model) (lis : List Nat) (c n : Nat) : Prop :=
  n < 25 ∨ n = c ∨ n = c + 1 ∨ n = c + 2 ∨
    ∃ b t, (b, t) ∈ lis.zip m.shown ∧ b ≤ n ∧ n < b + blockSize t (decide (m.editingId = t.id))

section
variable {m : Model} {w : World} {v5 v7 : String} {lis : List Nat} {c : Nat} (h : DocRep m w v5 v7 lis c)
include h

theorem DocRep.known_child {p x : Nat} (hp : Known m lis c p) (hx : x ∈ (w.node p).children) :
    Known m lis c x := by
  obtain ⟨_, hc0, hc1, hc2⟩ := h.counter
  rcases hp with hp | rfl | rfl | rfl | ⟨b, t, hbt, hb1, hb2⟩
  · rw [h.static p hp] at hx
    interval_cases p <;> simp [staticNode, staticNodeD, Model.dyn] at hx
    all_goals first
      | (left; omega)
      | (rcases hx with rfl | rfl <;> simp [Known])
      | skip
    obtain ⟨t, ht⟩ := forall₂_mem_zip h.blocks x hx
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, t, ht, le_refl _, by have := blockSize_pos t (decide (m.editingId = t.id)); omega⟩)))
  · rw [hc0] at hx; simp at hx; subst hx; simp [Known]
  · rw [hc1] at hx; simp at hx
  · rw [hc2] at hx; simp at hx
  · have hB := forall₂_zip h.blocks b t hbt
    obtain ⟨v2, ve, hn⟩ := hB.2
    obtain ⟨i, rfl⟩ : ∃ i, p = b + i := ⟨p - b, by omega⟩
    rw [hn i (by omega)] at hx
    have := blockNode_children_mem _ _ _ _ _ _ _ _ hx
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b, t, hbt, by omega, this.2⟩)))

theorem DocRep.known_of_go (hwf : ParentWF w) :
    ∀ f n, (World.ancestors.go w f n).getLast? = some 0 → Known m lis c n
  | 0, n, hl => by simp [World.ancestors.go] at hl
  | f + 1, n, hl => by
    simp only [World.ancestors.go] at hl
    split at hl
    · rename_i p hp
      by_cases he : World.ancestors.go w f p = []
      · rw [he] at hl; simp at hl; subst hl; left; omega
      · rw [List.getLast?_cons, List.getLast?_eq_some_getLast he] at hl
        have hp' : Known m lis c p := DocRep.known_of_go hwf f p (by rw [List.getLast?_eq_some_getLast he]; exact hl)
        exact h.known_child hp' (hwf.wf n p hp)
    · simp at hl; subst hl; left; omega

theorem DocRep.known_of_attached (hwf : ParentWF w) {n : Nat} (ha : w.attached n = true) :
    Known m lis c n := by
  simp only [World.attached, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ha
  exact h.known_of_go hwf _ n ha.2

end

end TodoMVC.Proof
