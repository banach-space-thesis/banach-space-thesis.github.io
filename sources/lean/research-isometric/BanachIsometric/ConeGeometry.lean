import BanachIsometric.LipschitzCone
import BanachIsometric.RadialHomeomorphism
import BanachIsometric.ExactFamilyTopology

/-!
# Exact geometry of the operator cone

The operator cone is defined on the whole ambient space. This gives the
Lipschitz extension used in the signed integral argument directly, and preserves
the common derivative exception set. The factorisation below is the actual
radial factorisation in the paper, before invoking any degree theorem.
-/

namespace BanachIsometric

open Set NormedSpace
open scoped NNReal

section General

variable {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem coneExtension_smul_nonneg (A : Metric.sphere (0 : V) 1 → W)
    {t : ℝ} (ht : 0 ≤ t) (x : V) : coneExtension A (t • x) = t • coneExtension A x := by
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases hx : x = 0
  · simp [hx]
  have htx : t • x ≠ 0 := smul_ne_zero ht0 hx
  rw [coneExtension_of_ne A _ htx, coneExtension_of_ne A x hx,
    norm_smul, Real.norm_of_nonneg ht, mul_smul]
  congr 3
  apply Subtype.ext
  exact normalize_smul_of_pos (lt_of_le_of_ne ht (Ne.symm ht0)) x

theorem map_coneExtension (L : W →L[ℝ] Z)
    (A : Metric.sphere (0 : V) 1 → W) (x : V) :
    L (coneExtension A x) = coneExtension (fun z => L (A z)) x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [coneExtension_of_ne A x hx, coneExtension_of_ne _ x hx, map_smul]

theorem radialGaugeMapInv_eq_smul_normalize (p : V → ℝ) (x : V) :
    radialGaugeMapInv p x = p x • normalize x := by
  rw [radialGaugeMapInv, NormedSpace.normalize, div_eq_mul_inv, mul_smul]

end General

namespace ExactTangentialFamily

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {g : V → ℝ} {p : E → ℝ}
  (A : ExactTangentialFamily E V g p)

/-- The paper's family `F_y`, defined globally using the same operator cone. -/
noncomputable def coneEvaluation (y : E) (x : V) : V := coneExtension A.maps x y

theorem coneEvaluation_eq (y : E) :
    A.coneEvaluation y = coneExtension (fun z => A.maps z y) := by
  funext x
  exact map_coneExtension (ContinuousLinearMap.apply ℝ V y) A.maps x

@[simp] theorem coneEvaluation_zero (y : E) : A.coneEvaluation y 0 = 0 := by
  simp [coneEvaluation]

theorem exists_lipschitz_operator_cone [FiniteDimensional ℝ V] :
    ∃ L : ℝ≥0, LipschitzWith L (coneExtension A.maps) := by
  obtain ⟨L, hL⟩ := A.maps_lipschitz
  exact exists_lipschitz_coneExtension hL

theorem exists_lipschitz_coneEvaluation [FiniteDimensional ℝ V] (y : E) :
    ∃ L : ℝ≥0, LipschitzWith L (A.coneEvaluation y) := by
  obtain ⟨L, hL⟩ := A.exists_lipschitz_operator_cone
  exact ⟨‖ContinuousLinearMap.apply ℝ V y‖₊ * L,
    (ContinuousLinearMap.apply ℝ V y).lipschitz.comp hL⟩

theorem gauge_coneEvaluation (hg : IsDefinitePositiveHomogeneous g) (y : E) (x : V) :
    g (A.coneEvaluation y x) = ‖x‖ * p y := by
  by_cases hx : x = 0
  · simp [hx, (hg.eq_zero_iff 0).mpr rfl]
  rw [coneEvaluation, coneExtension_of_ne A.maps x hx,
    ContinuousLinearMap.smul_apply, hg.smul_nonneg _ (norm_nonneg _), A.gauge_eq]

/-- The radial inverse sends `F_y` exactly to `p(y)` times the cone on `w_y`. -/
theorem radial_inverse_coneEvaluation (hg : IsDefinitePositiveHomogeneous g)
    {y : E} (hy : 0 < p y) (x : V) :
    radialGaugeMapInv g (A.coneEvaluation y x) =
      p y • coneExtension (fun z => ((A.direction ((hg.eq_zero_iff 0).mpr rfl) hy) z).val) x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [radialGaugeMapInv_eq_smul_normalize, A.gauge_coneEvaluation hg,
    coneEvaluation, coneExtension_of_ne A.maps x hx, ContinuousLinearMap.smul_apply,
    normalize_smul_of_pos (norm_pos_iff.mpr hx), coneExtension_of_ne _ x hx]
  change (‖x‖ * p y) • normalize (A.maps (coneDirection x hx) y) =
    p y • (‖x‖ • normalize (A.maps (coneDirection x hx) y))
  rw [← mul_smul, mul_comm]

/-- Actual factorisation through the cone on the normalised evaluation.
No equality of degrees is used as a premise. -/
theorem coneEvaluation_radial_factorization (hg : IsDefinitePositiveHomogeneous g)
    {y : E} (hy : 0 < p y) (x : V) :
    A.coneEvaluation y x = radialGaugeMap g
      (p y • coneExtension
        (fun z => ((A.direction ((hg.eq_zero_iff 0).mpr rfl) hy) z).val) x) := by
  rw [← A.radial_inverse_coneEvaluation hg hy x, radialGaugeMap_mapInv hg]

theorem coneEvaluation_image_ball (hg : IsDefinitePositiveHomogeneous g)
    {y : E} (hy : 0 < p y) :
    A.coneEvaluation y '' Metric.ball (0 : V) 1 ⊆ {v | g v < p y} := by
  rintro v ⟨x, hx, rfl⟩
  change g (A.coneEvaluation y x) < p y
  rw [A.gauge_coneEvaluation hg]
  have hx' : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  simpa using mul_lt_mul_of_pos_right hx' hy

theorem coneEvaluation_image_sphere (hg : IsDefinitePositiveHomogeneous g)
    (y : E) :
    A.coneEvaluation y '' Metric.sphere (0 : V) 1 ⊆ {v | g v = p y} := by
  rintro v ⟨x, hx, rfl⟩
  change g (A.coneEvaluation y x) = p y
  rw [A.gauge_coneEvaluation hg]
  have hx' : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  rw [hx', one_mul]

end ExactTangentialFamily

end BanachIsometric
