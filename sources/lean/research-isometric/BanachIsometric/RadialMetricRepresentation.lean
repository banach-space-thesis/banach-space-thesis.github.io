import BanachIsometric.MetricBallGauge
import BanachIsometric.FunctionalStarBody

/-! The radial profile of the original translation-invariant metric is
constructed from actual centered-ball geometry. Monotonicity, positivity,
continuity, and subadditivity follow from that same original metric. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [MetricSpace X]

/-- Every positive centered ball is either the whole space or an actual
sublevel of the specified homogeneous gauge. -/
def ClosedBallGaugeRepresentation (q : X → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → Metric.closedBall (0 : X) r = univ ∨
    ∃ a : ℝ, Metric.closedBall (0 : X) r = {x : X | q x ≤ a}

def ClosedBallsGaugeMonotone (q : X → ℝ) : Prop :=
  ∀ r : ℝ, ∀ x y : X, q x ≤ q y →
    y ∈ Metric.closedBall (0 : X) r → x ∈ Metric.closedBall (0 : X) r

theorem closedBallsGaugeMonotone_of_representation {q : X → ℝ}
    (hq : AlgebraicPositiveHomogeneous q) (hball : ClosedBallGaugeRepresentation q) :
    ClosedBallsGaugeMonotone q := by
  intro r x y hxy hy
  by_cases hr : 0 < r
  · rcases hball r hr with hwhole | ⟨a, ha⟩
    · rw [hwhole]
      exact mem_univ x
    · rw [ha] at hy ⊢
      exact hxy.trans hy
  · have hy0 : y = 0 := dist_eq_zero.mp (le_antisymm ((show dist y 0 ≤ r from hy).trans (le_of_not_gt hr)) dist_nonneg)
    have hqy : q y = 0 := (hq.eq_zero_iff y).mpr hy0
    have hx0 : x = 0 := (hq.eq_zero_iff x).mp (le_antisymm (hxy.trans_eq hqy) (hq.nonneg x))
    simpa only [hx0, hy0] using hy

omit [Module ℝ X] in
theorem distance_zero_mono_of_gauge {q : X → ℝ} (hball : ClosedBallsGaugeMonotone q)
    {x y : X} (hxy : q x ≤ q y) : dist x 0 ≤ dist y 0 := by
  exact hball (dist y 0) x y hxy (by change dist y 0 ≤ dist y 0; exact le_rfl)

omit [Module ℝ X] in
theorem distance_zero_eq_of_gauge_eq {q : X → ℝ} (hball : ClosedBallsGaugeMonotone q)
    {x y : X} (hxy : q x = q y) : dist x 0 = dist y 0 :=
  le_antisymm (distance_zero_mono_of_gauge hball hxy.le) (distance_zero_mono_of_gauge hball hxy.ge)

omit [MetricSpace X] in
theorem exists_gauge_unit [Nontrivial X] {q : X → ℝ} (hq : AlgebraicPositiveHomogeneous q) :
    ∃ e : X, q e = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hqx : q x ≠ 0 := (hq.eq_zero_iff x).not.mpr hx
  have hpos : 0 < q x := by have hn := hq.nonneg x; positivity
  refine ⟨(q x)⁻¹ • x, ?_⟩
  rw [hq.smul_nonneg _ (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hqx]

def radialProfile (e : X) (t : ℝ≥0) : ℝ≥0 := ⟨dist ((t : ℝ) • e) 0, dist_nonneg⟩

omit [MetricSpace X] in
theorem gauge_smul_unit {q : X → ℝ} (hq : AlgebraicPositiveHomogeneous q)
    {e : X} (he : q e = 1) (t : ℝ≥0) : q ((t : ℝ) • e) = t := by
  rw [hq.smul_nonneg _ t.coe_nonneg, he, mul_one]

theorem radialProfile_zero (e : X) : radialProfile e 0 = 0 := by
  apply Subtype.ext
  change dist ((0 : ℝ) • e) 0 = 0
  simp only [zero_smul, dist_self]

theorem radialProfile_pos {q : X → ℝ} (hq : AlgebraicPositiveHomogeneous q)
    {e : X} (he : q e = 1) {t : ℝ≥0} (ht : 0 < t) : 0 < radialProfile e t := by
  change 0 < dist ((t : ℝ) • e) 0
  apply dist_pos.mpr
  intro hz
  have ht0 : (t : ℝ) = 0 := by
    rw [← gauge_smul_unit hq he t, hz]
    exact (hq.eq_zero_iff 0).mpr rfl
  exact (NNReal.coe_pos.mpr ht).ne' ht0

theorem radialProfile_monotone {q : X → ℝ} (hq : AlgebraicPositiveHomogeneous q)
    (hball : ClosedBallsGaugeMonotone q) {e : X} (he : q e = 1) : Monotone (radialProfile e) := by
  intro s t hst
  change dist ((s : ℝ) • e) 0 ≤ dist ((t : ℝ) • e) 0
  apply distance_zero_mono_of_gauge hball
  rw [gauge_smul_unit hq he s, gauge_smul_unit hq he t]
  exact hst

theorem radialProfile_subadditive (hTI : TranslationInvariant (X := X)) (e : X) (s t : ℝ≥0) :
    radialProfile e (s + t) ≤ radialProfile e s + radialProfile e t := by
  change dist (((s : ℝ) + (t : ℝ)) • e) 0 ≤ dist ((s : ℝ) • e) 0 + dist ((t : ℝ) • e) 0
  rw [add_smul]
  have he := hTI ((s : ℝ) • e) 0 ((t : ℝ) • e)
  simp only [zero_add] at he
  exact (dist_triangle (((s : ℝ) • e) + (t : ℝ) • e) ((t : ℝ) • e) 0).trans_eq (by rw [he])

theorem continuous_radialProfile [ContinuousSMul ℝ X] (e : X) : Continuous (radialProfile e) := by
  have h : Continuous (fun t : ℝ≥0 => dist ((t : ℝ) • e) 0) :=
    (continuous_subtype_val.smul continuous_const).dist continuous_const
  exact h.subtype_mk _

theorem dist_eq_radialProfile {q : X → ℝ} (hq : AlgebraicPositiveHomogeneous q)
    (hTI : TranslationInvariant (X := X)) (hball : ClosedBallsGaugeMonotone q)
    {e : X} (he : q e = 1) (x y : X) :
    dist x y = radialProfile e ⟨q (x - y), hq.nonneg (x - y)⟩ := by
  rw [dist_eq_dist_sub_zero hTI]
  apply distance_zero_eq_of_gauge_eq hball
  rw [gauge_smul_unit hq he]
  rfl

theorem exists_radial_metric_profile [Nontrivial X] [ContinuousSMul ℝ X]
    {q : X → ℝ} (hq : AlgebraicPositiveHomogeneous q)
    (hTI : TranslationInvariant (X := X)) (hball : ClosedBallGaugeRepresentation q) :
    ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
      (∀ t, 0 < t → 0 < φ t) ∧ (∀ s t, φ (s + t) ≤ φ s + φ t) ∧
      ∀ x y : X, dist x y = φ ⟨q (x - y), hq.nonneg (x - y)⟩ := by
  obtain ⟨e, he⟩ := exists_gauge_unit hq
  have hMono := closedBallsGaugeMonotone_of_representation hq hball
  exact ⟨radialProfile e, continuous_radialProfile e, radialProfile_monotone hq hMono he,
    radialProfile_zero e, fun _ ht => radialProfile_pos hq he ht, radialProfile_subadditive hTI e,
    dist_eq_radialProfile hq hTI hMono he⟩

end
end BanachIsometric.MetricGeometry
