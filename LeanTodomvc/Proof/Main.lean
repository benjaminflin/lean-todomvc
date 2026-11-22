import LeanTodomvc.Proof.Init

/-!
# The invariant holds in every reachable state
-/

namespace TodoMVC
open JS DOM Mu Proof

theorem Proof.rep_s₀ : Rep ((loadModel []).route "") s₀ :=
  init_rep [] (by simp) (by simp) [] (Or.inl ⟨rfl, rfl⟩) ""

theorem Proof.step_rep_all {m : Model} {s : State} (h : Rep m s) (a : Action) :
    ∃ m', Rep m' (app.step s a) := by
  by_cases ha : a = .reload
  · subst ha
    exact ⟨_, init_rep m.todos h.model.nodup h.model.nonneg _
      (by rcases h.storage with ⟨hs, ht⟩ | hs
          · exact Or.inl ⟨hs, ht⟩
          · exact Or.inr hs) _⟩
  · exact step_rep h a ha

theorem Proof.rep_reachable {s : State} (hr : Reachable app.step s₀ s) : ∃ m, Rep m s := by
  induction hr with
  | refl => exact ⟨_, rep_s₀⟩
  | tail _ hst ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨a, rfl⟩ := hst
    exact step_rep_all hm a

/-- Every reachable state satisfies the invariants. -/
theorem invariant_holds : Sat specInvariant := by
  unfold Sat Mu.Sat specInvariant
  rw [mem_AG]
  intro t ht
  obtain ⟨m, hm⟩ := rep_reachable ht
  simpa [atom, sem] using invariant_of_rep hm

end TodoMVC
