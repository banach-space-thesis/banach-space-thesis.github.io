import BanachIsometric.HomogeneousGeometry

/-!
# The actual Lipschitz cone extension of a sphere-valued family

The codomain may be any real normed space, in particular the operator space in
Theorem 3.1. A sphere Lipschitz constant `C` and sphere bound `M` give the
global constant `M + 2*C`, with zero defined explicitly at the cone vertex.
-/

namespace BanachIsometric

open NormedSpace Set
open scoped NNReal

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def coneDirection (x : V) (hx : x ≠ 0) : Metric.sphere (0 : V) 1 :=
  ⟨normalize x, by simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize hx⟩

noncomputable def coneExtension (A : Metric.sphere (0 : V) 1 → W) (x : V) : W := by
  classical
  exact if hx : x = 0 then 0 else ‖x‖ • A (coneDirection x hx)

@[simp] theorem coneExtension_zero (A : Metric.sphere (0 : V) 1 → W) :
    coneExtension A 0 = 0 := by simp [coneExtension]

theorem coneExtension_of_ne (A : Metric.sphere (0 : V) 1 → W) (x : V) (hx : x ≠ 0) :
    coneExtension A x = ‖x‖ • A (coneDirection x hx) := by simp only [coneExtension, dif_neg hx]

theorem coneExtension_unit (A : Metric.sphere (0 : V) 1 → W)
    (u : Metric.sphere (0 : V) 1) : coneExtension A u.val = A u := by
  have hu : ‖u.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hu0 : u.val ≠ 0 := by intro hz; simp [hz] at hu
  rw [coneExtension_of_ne A u.val hu0, hu, one_smul]
  congr 1
  apply Subtype.ext
  exact normalize_eq_self_of_norm_eq_one hu

theorem norm_coneExtension_le {A : Metric.sphere (0 : V) 1 → W} {M : ℝ≥0}
    (hM : ∀ u, ‖A u‖ ≤ M) (x : V) : ‖coneExtension A x‖ ≤ (M : ℝ) * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  rw [coneExtension_of_ne A x hx, norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM (coneDirection x hx)) (norm_nonneg x)

theorem coneExtension_lipschitzWith {A : Metric.sphere (0 : V) 1 → W} {C M : ℝ≥0}
    (hC : LipschitzWith C A) (hM : ∀ u, ‖A u‖ ≤ M) :
    LipschitzWith (M + 2 * C) (coneExtension A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hcoef : (M : ℝ) ≤ ((M + 2 * C : ℝ≥0) : ℝ) := by
    push_cast
    nlinarith [C.coe_nonneg]
  by_cases hx : x = 0
  · subst x
    rw [coneExtension_zero, dist_zero_left, dist_zero_left]
    exact (norm_coneExtension_le hM y).trans
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg y))
  by_cases hy : y = 0
  · subst y
    rw [coneExtension_zero, dist_zero_right, dist_zero_right]
    exact (norm_coneExtension_le hM x).trans
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg x))
  let u := coneDirection x hx
  let v := coneDirection y hy
  have hdiff : ‖A u - A v‖ ≤ (C : ℝ) * ‖normalize x - normalize y‖ := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hC.dist_le_mul u v
  have hnorm : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  rw [dist_eq_norm, dist_eq_norm, coneExtension_of_ne A x hx, coneExtension_of_ne A y hy]
  change ‖‖x‖ • A u - ‖y‖ • A v‖ ≤ _
  have hdecomp : ‖x‖ • A u - ‖y‖ • A v =
      ‖x‖ • (A u - A v) + (‖x‖ - ‖y‖) • A v := by
    rw [smul_sub, sub_smul]
    abel
  calc
    ‖‖x‖ • A u - ‖y‖ • A v‖ ≤
        ‖‖x‖ • (A u - A v)‖ + ‖(‖x‖ - ‖y‖) • A v‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    _ = ‖x‖ * ‖A u - A v‖ + |‖x‖ - ‖y‖| * ‖A v‖ := by
      rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x), norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x‖ * ((C : ℝ) * ‖normalize x - normalize y‖) + ‖x - y‖ * (M : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hdiff (norm_nonneg x))
        (mul_le_mul hnorm (hM v) (norm_nonneg _) (norm_nonneg _))
    _ = (C : ℝ) * (‖x‖ * ‖normalize x - normalize y‖) + (M : ℝ) * ‖x - y‖ := by ring
    _ ≤ (C : ℝ) * (2 * ‖x - y‖) + (M : ℝ) * ‖x - y‖ := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (norm_mul_normalize_sub_le x y hy) C.coe_nonneg) _
    _ = ((M + 2 * C : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring

/-- Compactness supplies the bound needed above; it is not an additional
regularity hypothesis on a finite-dimensional exact family. -/
theorem exists_lipschitz_coneExtension [FiniteDimensional ℝ V]
    {A : Metric.sphere (0 : V) 1 → W} {C : ℝ≥0} (hC : LipschitzWith C A) :
    ∃ L : ℝ≥0, LipschitzWith L (coneExtension A) := by
  letI : CompactSpace (Metric.sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hC.continuous.norm.continuousOn
  let M : ℝ≥0 := ⟨max 0 B, le_max_left _ _⟩
  have hM : ∀ u, ‖A u‖ ≤ M := fun u =>
    (hB (mem_image_of_mem (fun z => ‖A z‖) (mem_univ u))).trans (le_max_right _ _)
  exact ⟨M + 2 * C, coneExtension_lipschitzWith hC hM⟩

end BanachIsometric
