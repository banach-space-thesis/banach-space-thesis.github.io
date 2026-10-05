import ThesisCommon.Analysis.WCGEllOneSeparableRange
import ThesisCommon.Analysis.LpOperators
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! The complete WCG support-reduction alternative, on actual ℓ₁(Γ,X).
Hahn–Banach scalarisation uses the same coordinatewise map as Lemma 4.14;
countable unions and the actual ℓ₁ expansion then give the block conclusion.
-/
noncomputable section
open Filter Topology TopologicalSpace
open scoped BigOperators ENNReal
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Scalar-to-vector support reduction for the actual ℓ₁ model. -/
theorem ellOne_operator_countable_support_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1, IsSeparable (Set.range S))
    (T : X →L[𝕜] lp (fun _ : Γ => X) 1) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : X, ∀ γ ∉ Λ, T x γ = 0 := by
  classical
  have hw : ∀ γ, ∃ x : X, (∃ y : X, T y γ ≠ 0) → T x γ ≠ 0 := by
    intro γ
    by_cases h : ∃ y : X, T y γ ≠ 0
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose x hx using hw
  choose φ hφ hφx using fun γ => exists_dual_vector'' 𝕜 (T (x γ) γ)
  let S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1 :=
    (lpDiagonal 1 φ 1 zero_le_one hφ).comp T
  obtain ⟨Λ, hΛ, hsupp⟩ := lp_separable_countable_support (𝕜 := 𝕜)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hsep S)
  refine ⟨Λ, hΛ, ?_⟩
  intro y γ hγ
  by_contra hy
  have hn : T (x γ) γ ≠ 0 := hx γ ⟨y, hy⟩
  have hz : S (x γ) γ = 0 := by
    by_contra hne
    exact hγ (hsupp (S (x γ)) ⟨x γ, rfl⟩ hne)
  simp only [S, ContinuousLinearMap.comp_apply, lpDiagonal_apply, hφx] at hz
  exact (norm_ne_zero_iff.mpr hn) (RCLike.ofReal_eq_zero.mp hz)

/-- WCG spaces have countable outgoing support under every operator into
the actual vector-valued ℓ₁ sum. -/
theorem IsWeaklyCompactlyGenerated.ellOne_operator_countable_support
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (T : X →L[𝕜] lp (fun _ : Γ => X) 1) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : X, ∀ γ ∉ Λ, T x γ = 0 :=
  ellOne_operator_countable_support_of_separable_scalar_ranges
    (fun S => hX.ellOne_operator_separable_range S) T

/-- Corollary 4.16's WCG alternative, with no cardinality restriction. -/
theorem IsWeaklyCompactlyGenerated.ellOne_countable_block_support
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (T : lp (fun _ : Γ => X) 1 →L[𝕜] lp (fun _ : Γ => X) 1)
    (Δ : Set Γ) (hΔ : Δ.Countable) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : lp (fun _ : Γ => X) 1,
      (∀ γ ∉ Δ, x γ = 0) → ∀ γ ∉ Λ, T x γ = 0 := by
  classical
  have hα (α : Γ) := hX.ellOne_operator_countable_support
    (T.comp (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := 1) (E := fun _ : Γ => X) α))
  choose A hA hTA using hα
  let Λ : Set Γ := ⋃ α ∈ Δ, A α
  refine ⟨Λ, hΔ.biUnion (fun α _ => hA α), ?_⟩
  intro x hx γ hγ
  let R : lp (fun _ : Γ => X) 1 →L[𝕜] X := (lpCoordinate 1 γ).comp T
  have hz (α : Γ) : R (lp.single 1 α (x α)) = 0 := by
    by_cases hαΔ : α ∈ Δ
    · have hγα : γ ∉ A α := by
        intro hm
        exact hγ (Set.mem_iUnion.mpr ⟨α, Set.mem_iUnion.mpr ⟨hαΔ, hm⟩⟩)
      simpa only [R, ContinuousLinearMap.comp_apply, lpCoordinate_apply,
        lp.singleContinuousLinearMap_apply] using hTA α (x α) γ hγα
    · simp only [hx α hαΔ, lp.single_zero, map_zero]
  have ht := (R.continuous.tendsto x).comp (lp.hasSum_single (by norm_num) x)
  have hs : Tendsto (fun F : Finset Γ => R (∑ α ∈ F, lp.single 1 α (x α)))
      atTop (𝓝 0) := by
    simpa only [map_sum, hz, Finset.sum_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Finset Γ => (0 : X)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hs

end ThesisCommon
