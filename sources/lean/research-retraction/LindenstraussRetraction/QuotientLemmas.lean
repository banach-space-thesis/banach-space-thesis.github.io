import LindenstraussRetraction.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Equivalent quotient-map formulations

These theorems verify that the open-unit-ball definition used in the statements
has the surjectivity and quotient-norm meaning specified in Section 2.
-/

noncomputable section

namespace LindenstraussRetraction

universe u v w

variable {𝕜 : Type w} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

private theorem norm_inv_real_smul (r : ℝ) (hr : 0 < r) (x : E) :
    ‖(r : 𝕜)⁻¹ • x‖ = ‖x‖ / r := by
  simp [norm_smul, abs_of_pos hr, div_eq_mul_inv, mul_comm]

private theorem norm_real_smul (r : ℝ) (hr : 0 ≤ r) (x : E) :
    ‖(r : 𝕜) • x‖ = r * ‖x‖ := by
  simp [norm_smul, abs_of_nonneg hr]

namespace IsNormQuotient

/-- A norm quotient is contractive, as required by the quotient norm. -/
theorem norm_le {q : E →L[𝕜] W} (h : IsNormQuotient q) (x : E) :
    ‖q x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let r : ℝ := ‖x‖ + ε
  have hr : 0 < r := add_pos_of_nonneg_of_pos (norm_nonneg _) hε
  have hx : (r : 𝕜)⁻¹ • x ∈ Metric.ball (0 : E) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_inv_real_smul r hr]
    apply (div_lt_one hr).2
    dsimp [r]
    linarith
  have hqx : q ((r : 𝕜)⁻¹ • x) ∈ Metric.ball (0 : W) 1 := by
    rw [← h]
    exact ⟨_, hx, rfl⟩
  rw [Metric.mem_ball, dist_zero_right, q.map_smul,
    norm_inv_real_smul r hr] at hqx
  exact ((div_lt_one hr).1 hqx).le

/-- Every strict upper bound on the norm of a target admits a lift below it. -/
theorem exists_lift_norm_lt {q : E →L[𝕜] W} (h : IsNormQuotient q)
    (y : W) {r : ℝ} (hyr : ‖y‖ < r) :
    ∃ x : E, q x = y ∧ ‖x‖ < r := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hyr
  have hy : (r : 𝕜)⁻¹ • y ∈ Metric.ball (0 : W) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_inv_real_smul r hr]
    exact (div_lt_one hr).2 hyr
  rw [← h] at hy
  obtain ⟨x, hx, hqx⟩ := hy
  refine ⟨(r : 𝕜) • x, ?_, ?_⟩
  · rw [q.map_smul, hqx, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast hr.ne'
  · rw [norm_real_smul r hr.le]
    have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hx
    simpa using (mul_lt_mul_of_pos_left hx' hr)

/-- The open-ball image equality holds at every positive radius. -/
theorem image_ball {q : E →L[𝕜] W} (h : IsNormQuotient q)
    {r : ℝ} (_hr : 0 < r) :
    q '' Metric.ball (0 : E) r = Metric.ball (0 : W) r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ < r := by simpa [Metric.mem_ball] using hx
    simpa [Metric.mem_ball] using lt_of_le_of_lt (h.norm_le x) hx'
  · intro hy
    have hy' : ‖y‖ < r := by simpa [Metric.mem_ball] using hy
    obtain ⟨x, hqx, hx⟩ := h.exists_lift_norm_lt y hy'
    exact ⟨x, by simpa [Metric.mem_ball] using hx, hqx⟩

/-- In particular, the open-ball condition already contains surjectivity. -/
theorem surjective {q : E →L[𝕜] W} (h : IsNormQuotient q) :
    Function.Surjective q := by
  intro y
  obtain ⟨x, hx, _⟩ := h.exists_lift_norm_lt y (lt_add_one ‖y‖)
  exact ⟨x, hx⟩

/-- Lifts of a unit vector can be chosen with norm arbitrarily close to one. -/
theorem exists_sphere_lift {q : E →L[𝕜] W} (h : IsNormQuotient q)
    (y : UnitSphere W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : E, q x = y.val ∧ ‖x‖ < 1 + δ := by
  apply h.exists_lift_norm_lt
  rw [y.property]
  linarith

/-- The quotient norm is the infimum of the norms of all lifts. -/
theorem norm_eq_sInf {q : E →L[𝕜] W} (h : IsNormQuotient q) (y : W) :
    ‖y‖ = sInf {r : ℝ | ∃ x : E, q x = y ∧ ‖x‖ = r} := by
  let A : Set ℝ := {r : ℝ | ∃ x : E, q x = y ∧ ‖x‖ = r}
  have hA : A.Nonempty := by
    obtain ⟨x, hx⟩ := h.surjective y
    exact ⟨‖x‖, x, hx, rfl⟩
  have hB : BddBelow A := ⟨0, by
    rintro r ⟨x, _, rfl⟩
    exact norm_nonneg x⟩
  apply le_antisymm
  · apply le_csInf hA
    rintro r ⟨x, hx, rfl⟩
    rw [← hx]
    exact h.norm_le x
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, hnorm⟩ := h.exists_lift_norm_lt y
      (lt_add_of_pos_right ‖y‖ hε)
    exact (csInf_le hB (show ‖x‖ ∈ A from ⟨x, hx, rfl⟩)).trans hnorm.le

end IsNormQuotient

/-- Contractivity and arbitrarily sharp lifts are equivalent to the paper's
open-unit-ball convention. -/
theorem isNormQuotient_iff_norm_le_and_lifts (q : E →L[𝕜] W) :
    IsNormQuotient q ↔
      (∀ x : E, ‖q x‖ ≤ ‖x‖) ∧
        (∀ (y : W) (r : ℝ), ‖y‖ < r → ∃ x : E, q x = y ∧ ‖x‖ < r) := by
  constructor
  · intro h
    exact ⟨h.norm_le, fun y _ hyr => h.exists_lift_norm_lt y hyr⟩
  · rintro ⟨hnorm, hlift⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hx
      simpa [Metric.mem_ball] using lt_of_le_of_lt (hnorm x) hx'
    · intro hy
      have hy' : ‖y‖ < 1 := by simpa [Metric.mem_ball] using hy
      obtain ⟨x, hx, hnorm⟩ := hlift y 1 hy'
      exact ⟨x, by simpa [Metric.mem_ball] using hnorm, hx⟩

/-- This is the infimum formulation given explicitly in the manuscript.
Surjectivity supplies nonempty fibers, so no convention for an empty real
infimum enters the characterization. -/
theorem isNormQuotient_iff_surjective_norm_eq_sInf (q : E →L[𝕜] W) :
    IsNormQuotient q ↔ Function.Surjective q ∧
      ∀ y : W, ‖y‖ = sInf {r : ℝ | ∃ x : E, q x = y ∧ ‖x‖ = r} := by
  constructor
  · intro h
    exact ⟨h.surjective, h.norm_eq_sInf⟩
  · rintro ⟨hsurj, hinf⟩
    apply (isNormQuotient_iff_norm_le_and_lifts q).2
    constructor
    · intro x
      rw [hinf]
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro r ⟨z, _, rfl⟩
        exact norm_nonneg z
      · exact ⟨x, rfl, rfl⟩
    · intro y r hyr
      have hA : ({s : ℝ | ∃ x : E, q x = y ∧ ‖x‖ = s}).Nonempty := by
        obtain ⟨x, hx⟩ := hsurj y
        exact ⟨‖x‖, x, hx, rfl⟩
      rw [hinf] at hyr
      obtain ⟨s, ⟨x, hx, hnorm⟩, hsr⟩ := exists_lt_of_csInf_lt hA hyr
      exact ⟨x, hx, hnorm ▸ hsr⟩

end LindenstraussRetraction
