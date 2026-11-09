import SurveyStatements.P2InvariantQuotient
import SurveyStatements.P2EllOneRows
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Exact bounded-row matrix units on a genuine quotient give bounded ell-one unit-vector lifts. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SurveyStatements.P2
universe v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem exists_ellOne_unit_lifts_of_matrixUnits (N : Submodule ℂ X)
    [IsClosed (N : Set X)]
    (U : ℕ → ℕ → (X ⧸ N) →L[ℂ] (X ⧸ N))
    (hmul : ∀ i j k l, U i j * U k l = if j = k then U i l else 0)
    (hne : U 0 0 ≠ 0) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hrow : ∀ (F : Finset ℕ) (a : ℕ → ℂ), (∀ j ∈ F, ‖a j‖ ≤ 1) →
      ‖∑ j ∈ F, a j • U 0 j‖ ≤ C)
    (hcol : ∀ i, ‖U i 0‖ ≤ D) :
    ∃ (Θ : X →L[ℂ] lp (fun _ : ℕ => ℂ) 1) (x : ℕ → X) (B : ℝ),
      0 ≤ B ∧ (∀ i, ‖x i‖ ≤ B) ∧ (∀ i, Θ (x i) = lp.single 1 i 1) := by
  classical
  have hex : ∃ y : X ⧸ N, U 0 0 y ≠ 0 := by
    by_contra hbad
    push_neg at hbad
    apply hne
    ext y
    simpa only [ContinuousLinearMap.zero_apply] using hbad y
  obtain ⟨y, hy⟩ := hex
  let z₀ := U 0 0 y
  have hz₀ : z₀ ≠ 0 := hy
  have hfix : U 0 0 z₀ = z₀ := by
    change (U 0 0 * U 0 0) y = U 0 0 y
    rw [hmul]
    simp
  obtain ⟨g, hg, hgz⟩ := exists_dual_vector ℂ z₀ hz₀
  let φ : (X ⧸ N) →L[ℂ] ℂ := ((‖z₀‖ : ℂ)⁻¹) • g
  have hφz : φ z₀ = 1 := by
    change (‖z₀‖ : ℂ)⁻¹ * g z₀ = 1
    rw [hgz]
    exact inv_mul_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hz₀)
  let z : ℕ → X ⧸ N := fun i => U i 0 z₀
  have hzbound : ∀ i, ‖z i‖ ≤ D * ‖z₀‖ := fun i =>
    ((U i 0).le_opNorm z₀).trans (mul_le_mul_of_nonneg_right (hcol i) (norm_nonneg z₀))
  choose x hx hnx using fun i => Submodule.Quotient.norm_mk_lt (z i) zero_lt_one
  let Θ := (rowEllOneMap (U 0) C hC hrow φ).comp (quotientProjection N)
  refine ⟨Θ, x, D * ‖z₀‖ + 1,
    add_nonneg (mul_nonneg hD (norm_nonneg z₀)) zero_le_one, ?_, ?_⟩
  · intro i
    exact (hnx i).le.trans (add_le_add_right (hzbound i) 1)
  · intro i
    apply lp.ext
    funext j
    change φ (U 0 j (Submodule.Quotient.mk (x i))) =
      (lp.single (E := fun _ : ℕ => ℂ) 1 i 1) j
    rw [hx i]
    change φ ((U 0 j * U i 0) z₀) = _
    rw [hmul]
    by_cases hji : j = i
    · simp only [if_pos hji, hfix, hφz]
      simp [lp.single_apply, hji]
    · simp only [if_neg hji, ContinuousLinearMap.zero_apply, map_zero]
      simp [lp.single_apply, hji]

end SurveyStatements.P2
