import SurveyStatements.P1Geometry
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Positivity

/-!
Normalization, almost-isometric transfer and the dense-subspace reduction
for Problem 1. These results have no dependency on the main theorem.
-/

noncomputable section

set_option autoImplicit false

namespace SurveyStatements.P1

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Normalization using the ambient complex scalar action. -/
def unitNormalize (x : X) : X := (‖x‖ : ℂ)⁻¹ • x

@[simp] theorem norm_unitNormalize {x : X} (hx : x ≠ 0) : ‖unitNormalize x‖ = 1 := by
  exact norm_smul_inv_norm hx

@[simp] theorem norm_smul_unitNormalize (x : X) :
    (‖x‖ : ℂ) • unitNormalize x = x := by
  by_cases hx : x = 0
  · simp [hx, unitNormalize]
  · have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
    simp [unitNormalize, smul_smul, hn]

theorem unitNormalize_map (T : E →ₗᵢ[ℂ] X) (x : E) :
    T (unitNormalize x) = unitNormalize (T x) := by
  simp only [unitNormalize, T.map_smul, T.norm_map]

theorem norm_unitNormalize_sub_self {x : X} (hx : x ≠ 0) :
    ‖unitNormalize x - x‖ = |1 - ‖x‖| := by
  have hid : unitNormalize x - x = ((1 - ‖x‖ : ℝ) : ℂ) • unitNormalize x := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul,
      norm_smul_unitNormalize]
  rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_unitNormalize hx, mul_one]

/-- Normalizing a nearby nonzero vector doubles its error at most. -/
theorem norm_unitNormalize_sub_le {x y : X} (hx : x ≠ 0) (hy : ‖y‖ = 1) :
    ‖unitNormalize x - y‖ ≤ 2 * ‖x - y‖ := by
  have h1 := norm_sub_le (unitNormalize x) x
  have h2 := norm_add_le (unitNormalize x - x) (x - y)
  have h3 := abs_norm_sub_norm_le x y
  rw [hy, abs_sub_comm] at h3
  rw [norm_unitNormalize_sub_self hx] at h2
  rw [sub_add_sub_cancel] at h2
  linarith

/-- Every unit vector in the closure of an isometric image can be approximated
by unit vectors in the image. -/
theorem denseRange_unit_approximation (T : E →ₗᵢ[ℂ] X) (hT : DenseRange T)
    {x : X} (hx : ‖x‖ = 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ u : E, ‖u‖ = 1 ∧ ‖T u - x‖ < 2 * δ := by
  obtain ⟨v, hv⟩ := hT.exists_dist_lt x hδ
  have hv' : ‖T v - x‖ < δ := by simpa [dist_eq_norm, norm_sub_rev] using hv
  have hTv : T v ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg, hx] at hv'
    linarith
  have hv0 : v ≠ 0 := by
    intro h
    exact hTv (by simp [h])
  refine ⟨unitNormalize v, norm_unitNormalize hv0, ?_⟩
  rw [unitNormalize_map]
  exact (norm_unitNormalize_sub_le hTv hx).trans_lt (by linarith)

/-- The completion-and-density step in the source: any separated unit sequence
in the completion produces a separated unit sequence in the dense subspace.
Only an isometry with dense range is needed. -/
theorem denseRange_separation_transfer (T : E →ₗᵢ[ℂ] X) (hT : DenseRange T)
    {ε : ℝ} (hε : 0 < ε) {x : ℕ → X} (hx : ∀ n, ‖x n‖ = 1)
    (hs : IsToroidallySeparated ε x) :
    ∃ η : ℝ, 0 < η ∧ ∃ u : ℕ → E,
      (∀ n, ‖u n‖ = 1) ∧ IsToroidallySeparated η u := by
  let δ : ℝ := min (ε / 8) (1 / 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    have h := min_le_right (ε / 8) (1 / 4 : ℝ)
    dsimp [δ]
    linarith
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hchoices : ∀ n, ∃ u : E, ‖u‖ = 1 ∧ ‖T u - x n‖ < 2 * δ :=
    fun n => denseRange_unit_approximation T hT (hx n) hδ hδ1
  choose u hu hd using hchoices
  refine ⟨ε - 4 * δ, by linarith, u, hu, ?_⟩
  intro n m hnm θ hθ
  have h1 := hs n m hnm θ hθ
  have h2 := phase_norm_perturbation (x n) (x m) (T (u n)) (T (u m)) hθ
  have hn : ‖x n - T (u n)‖ < 2 * δ := by simpa [norm_sub_rev] using hd n
  have hm : ‖x m - T (u m)‖ < 2 * δ := by simpa [norm_sub_rev] using hd m
  have hmap : ‖T (u n) - θ • T (u m)‖ = ‖u n - θ • u m‖ := by
    rw [← T.map_smul, ← T.map_sub, T.norm_map]
  rw [hmap] at h2
  linarith

end SurveyStatements.P1
