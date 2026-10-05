import ThesisCommon.Analysis.L1FiniteMaximumCuts
import ThesisCommon.Analysis.L1DyadicEmbeddingMass

/-! Persistent dyadic maximum mass gives finite measurable disjoint cuts at
arbitrarily fine levels. These cuts are constructed level by level; no nestedness
between different levels or complemented L1 copy is claimed here. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped BigOperators Topology
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem exists_l1DyadicMaximum_disjoint_cuts
    (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ) (n : ℕ) :
    ∃ (A : Fin (2 ^ n) → Set X) (hA : ∀ i, MeasurableSet (A i)),
      Pairwise (Disjoint on A) ∧ (⋃ i, A i) = Set.univ ∧
      (∑ i : Fin (2 ^ n), ‖lpCut (A i) (hA i) (T (l1DyadicIndicator 𝕜 n i))‖) =
        l1DyadicMaximumMass T n :=
  exists_l1FiniteMaximum_disjoint_cuts (pow_pos (by norm_num) n)
    (fun i => T (l1DyadicIndicator 𝕜 n i))

theorem exists_disjoint_cuts_of_persistentDyadicMaximumMass
    {T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] Lp 𝕜 1 μ}
    (hT : HasPersistentDyadicMaximumMass T) :
    ∃ ε > 0, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ m,
      ∃ (A : Fin (2 ^ σ m) → Set X) (hA : ∀ i, MeasurableSet (A i)),
        Pairwise (Disjoint on A) ∧ (⋃ i, A i) = Set.univ ∧
        ε ≤ ∑ i : Fin (2 ^ σ m),
          ‖lpCut (A i) (hA i) (T (l1DyadicIndicator 𝕜 (σ m) i))‖ := by
  obtain ⟨ε, hε, σ, hσ, hm⟩ := hasPersistentDyadicMaximumMass_subsequence hT
  refine ⟨ε, hε, σ, hσ, fun m => ?_⟩
  obtain ⟨A, hA, hd, hu, he⟩ := exists_l1DyadicMaximum_disjoint_cuts T (σ m)
  exact ⟨A, hA, hd, hu, he.symm ▸ hm m⟩

omit [MeasurableSpace X] in
theorem exists_l1Dyadic_projection_branch_disjoint_levels
    (P : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩) :
    ∃ (T : IntervalLp 𝕜 ⟨1, le_rfl⟩ →L[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩)
      (σ : ℕ → ℕ),
      (T = P ∨ T = ContinuousLinearMap.id 𝕜 _ - P) ∧ StrictMono σ ∧
      Tendsto (fun m => intervalLpDyadicRadius (σ m)) atTop (𝓝 0) ∧ ∀ m,
      ∃ (A : Fin (2 ^ σ m) → Set ℝ) (hA : ∀ i, MeasurableSet (A i)),
        Pairwise (Disjoint on A) ∧ (⋃ i, A i) = Set.univ ∧
        (1 / 2 : ℝ) ≤ ∑ i : Fin (2 ^ σ m),
          ‖lpCut (A i) (hA i) (T (l1DyadicIndicator 𝕜 (σ m) i))‖ := by
  obtain ⟨T, σ, hbranch, hσ, hm, hlim⟩ := exists_l1DyadicMaximumMass_branch_levels P
  refine ⟨T, σ, hbranch, hσ, hlim, fun m => ?_⟩
  obtain ⟨A, hA, hd, hu, he⟩ := exists_l1DyadicMaximum_disjoint_cuts T (σ m)
  exact ⟨A, hA, hd, hu, he.symm ▸ hm m⟩

end ThesisCommon
