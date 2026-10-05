import ThesisCommon.Analysis.SetMappingDefinitions
import ThesisCommon.Analysis.FactorNormalization

/-! Full-cardinality selection of a common factorisation branch. The uniform
case uses only a two-piece partition; countable cofinality is excluded only
when choosing a common bound from initially unbounded factorisations.
-/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ : Type u} {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem full_cardinal_predicate_choice (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (Λ : Set Γ) (hΛ : Cardinal.mk Λ = Cardinal.mk Γ) (P Q : Γ → Prop)
    (hPQ : ∀ γ ∈ Λ, P γ ∨ Q γ) :
    (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧ ∀ γ ∈ H, P γ) ∨
    (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧ ∀ γ ∈ H, Q γ) := by
  classical
  let A := {γ | γ ∈ Λ ∧ P γ}
  let B := Λ \ A
  by_cases hA : Cardinal.mk A = Cardinal.mk Γ
  · exact Or.inl ⟨A, fun _ h => h.1, hA, fun _ h => h.2⟩
  · have hB : Cardinal.mk B = Cardinal.mk Γ := by
      apply (Cardinal.mk_set_le B).antisymm
      by_contra hn
      have hltA := lt_of_le_of_ne (Cardinal.mk_set_le A) hA
      have hltB := lt_of_not_ge hn
      have hcover : Λ = A ∪ B := by
        ext γ
        simp only [A, B, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
        tauto
      have hsmall := (Cardinal.mk_union_le A B).trans_lt
        (Cardinal.add_lt_of_lt hΓ hltA hltB)
      rw [← hcover, hΛ] at hsmall
      exact lt_irrefl _ hsmall
    refine Or.inr ⟨B, fun _ h => h.1, hB, ?_⟩
    intro γ hγ
    exact (hPQ γ hγ.1).resolve_left (fun hp => hγ.2 ⟨hγ.1, hp⟩)

theorem full_cardinal_factor_branch (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (Λ : Set Γ) (hΛ : Cardinal.mk Λ = Cardinal.mk Γ)
    (F : Γ → X →L[𝕜] X) {C : ℝ}
    (hF : ∀ γ ∈ Λ, FactorsIdentityWith (F γ) X C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - F γ) X C) :
    (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧
      ∀ γ ∈ H, FactorsIdentityWith (F γ) X C) ∨
    (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧
      ∀ γ ∈ H, FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - F γ) X C) :=
  full_cardinal_predicate_choice hΓ Λ hΛ _ _ hF

theorem full_cardinal_bounded_factor_branch (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof)
    (Λ : Set Γ) (hΛ : Cardinal.mk Λ = Cardinal.mk Γ)
    (F : Γ → X →L[𝕜] X)
    (hF : ∀ γ ∈ Λ, FactorsIdentity (F γ) X ∨
      FactorsIdentity (ContinuousLinearMap.id 𝕜 X - F γ) X) :
    ∃ C : ℝ, 1 ≤ C ∧
      ((∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ γ ∈ H, FactorsIdentityWith (F γ) X C) ∨
      (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ γ ∈ H, FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - F γ) X C)) := by
  classical
  let A : ℕ → Set Γ := fun n => {γ | γ ∈ Λ ∧
    (FactorsIdentityWith (F γ) X (max 1 (n : ℝ)) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - F γ) X (max 1 (n : ℝ)))}
  have hcover : Λ = ⋃ n, A n := by
    ext γ
    constructor
    · intro hγ
      rcases hF γ hγ with hf | hf
      · obtain ⟨C, _, hC⟩ := (factorsIdentity_iff_exists_bound (F γ)).mp hf
        obtain ⟨n, hn⟩ := exists_nat_ge C
        exact Set.mem_iUnion.mpr ⟨n, hγ, Or.inl (hC.mono (hn.trans (le_max_right _ _)))⟩
      · obtain ⟨C, _, hC⟩ :=
          (factorsIdentity_iff_exists_bound (ContinuousLinearMap.id 𝕜 X - F γ)).mp hf
        obtain ⟨n, hn⟩ := exists_nat_ge C
        exact Set.mem_iUnion.mpr ⟨n, hγ, Or.inr (hC.mono (hn.trans (le_max_right _ _)))⟩
    · intro hγ
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hγ
      exact hn.1
  obtain ⟨n, hn⟩ := countable_union_cofinal_pigeonhole hΓ hcof Λ hΛ A hcover
  refine ⟨max 1 (n : ℝ), le_max_left _ _, ?_⟩
  rcases full_cardinal_factor_branch hΓ (A n) hn F (fun _ h => h.2) with h | h
  · obtain ⟨H, hH, hcard, hf⟩ := h
    exact Or.inl ⟨H, fun γ hγ => (hH hγ).1, hcard, hf⟩
  · obtain ⟨H, hH, hcard, hf⟩ := h
    exact Or.inr ⟨H, fun γ hγ => (hH hγ).1, hcard, hf⟩

end ThesisCommon
