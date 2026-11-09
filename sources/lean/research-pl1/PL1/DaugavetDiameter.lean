import PL1.DaugavetRealification
import PL1.IntrinsicExposedPoint
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Diameter two for slices of the actual intrinsic unit balls

The slice criterion gives points almost distance two apart in each normalized
real-part slice. All intrinsic specializations retain the original graph norm.
The underlying-real statements quantify over the full real continuous dual.
-/

noncomputable section
open Filter
open scoped Topology

namespace PL1.Daugavet

variable {K E : Type*} [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]

/-- A real-part slice of the closed unit ball; normalization and positive
thickness are explicit hypotheses of the theorems below. -/
def realPartSlice (φ : E →L[K] K) (α : ℝ) : Set E :=
  {x | ‖x‖ ≤ 1 ∧ 1 - α < RCLike.re (φ x)}

theorem dist_le_two_of_mem_realPartSlice {φ : E →L[K] K} {α : ℝ}
    {x y : E} (hx : x ∈ realPartSlice φ α) (hy : y ∈ realPartSlice φ α) :
    dist x y ≤ 2 := by
  rw [dist_eq_norm]
  have hn := norm_sub_le x y
  linarith [hx.1, hy.1]

theorem isBounded_realPartSlice (φ : E →L[K] K) (α : ℝ) :
    Bornology.IsBounded (realPartSlice φ α) :=
  Metric.isBounded_iff.mpr ⟨2, fun _ hx _ hy => dist_le_two_of_mem_realPartSlice hx hy⟩

/-- Every prescribed unit vector has points almost distance two away inside
any normalized real-part slice. -/
theorem SliceCriterion.exists_far_in_realPartSlice (hs : SliceCriterion K E)
    (φ : E →L[K] K) (hφ : ‖φ‖ = 1) {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (x : E) (hx : ‖x‖ = 1) :
    ∃ y ∈ realPartSlice φ α, 2 - ε < dist x y := by
  obtain ⟨y, hy, hφy, hxy⟩ := hs (-x) (by simpa only [norm_neg] using hx)
    φ hφ (min α ε) (lt_min hα hε)
  refine ⟨y, ⟨hy, ?_⟩, ?_⟩
  · exact lt_of_le_of_lt (by linarith [min_le_left α ε]) hφy
  · have hn : dist x y = ‖-x + y‖ := by
      rw [dist_eq_norm, norm_sub_rev, sub_eq_add_neg, add_comm]
    rw [hn]
    exact lt_of_le_of_lt (by linarith [min_le_right α ε]) hxy

/-- Explicit pairs in each normalized slice approach the maximum distance two. -/
theorem SliceCriterion.exists_dist_gt_in_realPartSlice (hs : SliceCriterion K E)
    (φ : E →L[K] K) (hφ : ‖φ‖ = 1) {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ x ∈ realPartSlice φ α, ∃ y ∈ realPartSlice φ α, 2 - ε < dist x y := by
  obtain ⟨x, hx, hφx⟩ := exists_unit_re_apply_gt φ hφ
    (lt_min (half_pos hα) (by norm_num : (0 : ℝ) < 1 / 2))
    (lt_of_le_of_lt (min_le_right (α / 2) (1 / 2)) (by norm_num))
  obtain ⟨y, hy, hxy⟩ := hs.exists_far_in_realPartSlice φ hφ hα hε x hx
  exact ⟨x, ⟨hx.le, lt_of_le_of_lt (by linarith [min_le_left (α / 2) (1 / 2)]) hφx⟩,
    y, hy, hxy⟩

/-- Each normalized real-part slice of the closed unit ball has diameter exactly two. -/
theorem SliceCriterion.diam_realPartSlice (hs : SliceCriterion K E)
    (φ : E →L[K] K) (hφ : ‖φ‖ = 1) {α : ℝ} (hα : 0 < α) :
    Metric.diam (realPartSlice φ α) = 2 := by
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le (by norm_num)
      (fun _ hx _ hy => dist_le_two_of_mem_realPartSlice hx hy)
  · by_contra! hlt
    obtain ⟨x, hx, y, hy, hxy⟩ := hs.exists_dist_gt_in_realPartSlice φ hφ hα
      (sub_pos.mpr hlt)
    have hd := Metric.dist_le_diam_of_mem (isBounded_realPartSlice φ α) hx hy
    linarith

/-- Every normalized real-part slice has metric diameter two. -/
def SliceDiameterTwo (K E : Type*) [RCLike K] [NormedAddCommGroup E]
    [NormedSpace K E] : Prop :=
  ∀ (φ : E →L[K] K), ‖φ‖ = 1 → ∀ {α : ℝ}, 0 < α →
    Metric.diam (realPartSlice φ α) = 2

theorem SliceCriterion.sliceDiameterTwo (hs : SliceCriterion K E) : SliceDiameterTwo K E :=
  fun φ hφ _ hα => hs.diam_realPartSlice φ hφ hα

/-- Maximizing sequences can remain asymptotically distance two from any
prescribed unit vector. In particular, a maximizer cannot be strongly exposed. -/
theorem SliceCriterion.exists_maximizing_sequence_far (hs : SliceCriterion K E)
    (φ : E →L[K] K) (hφ : ‖φ‖ = 1) (x : E) (hx : ‖x‖ = 1) :
    ∃ y : ℕ → E, (∀ n, ‖y n‖ ≤ 1) ∧
      Tendsto (fun n => RCLike.re (φ (y n))) atTop (𝓝 1) ∧
      Tendsto (fun n => dist x (y n)) atTop (𝓝 2) ∧
      ¬ Tendsto y atTop (𝓝 x) := by
  have hex (n : ℕ) : ∃ y ∈ realPartSlice φ (1 / ((n : ℝ) + 1)),
      2 - 1 / ((n : ℝ) + 1) < dist x y :=
    hs.exists_far_in_realPartSlice φ hφ (by positivity) (by positivity) x hx
  choose y hy hd using hex
  have hupper (n : ℕ) : RCLike.re (φ (y n)) ≤ 1 :=
    (RCLike.re_le_norm _).trans ((φ.le_opNorm _).trans (by simpa only [hφ, one_mul] using (hy n).1))
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hre : Tendsto (fun n => RCLike.re (φ (y n))) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [sub_zero] using tendsto_const_nhds.sub hinv)
      tendsto_const_nhds (fun n => (hy n).2.le) hupper
  have hdist : Tendsto (fun n => dist x (y n)) atTop (𝓝 2) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [sub_zero] using tendsto_const_nhds.sub hinv) tendsto_const_nhds
      (fun n => (hd n).le)
    intro n
    change dist x (y n) ≤ 2
    rw [dist_eq_norm]
    have hn := norm_sub_le x (y n)
    linarith [(hy n).1]
  refine ⟨y, fun n => (hy n).1, hre, hdist, ?_⟩
  intro hconv
  have hzero : Tendsto (fun n => dist x (y n)) atTop (𝓝 0) := by
    simpa only [dist_self] using (tendsto_const_nhds (x := x)).dist hconv
  have h02 : (0 : ℝ) = 2 := tendsto_nhds_unique hzero hdist
  norm_num at h02

/-- The sequential property required for strong exposure fails for every
normalized functional and every unit vector. -/
theorem SliceCriterion.not_strongly_exposes (hs : SliceCriterion K E)
    (φ : E →L[K] K) (hφ : ‖φ‖ = 1) (x : E) (hx : ‖x‖ = 1) :
    ¬ (∀ y : ℕ → E, (∀ n, ‖y n‖ ≤ 1) →
      Tendsto (fun n => RCLike.re (φ (y n))) atTop (𝓝 1) → Tendsto y atTop (𝓝 x)) := by
  obtain ⟨y, hy, hre, _, hnot⟩ := hs.exists_maximizing_sequence_far φ hφ x hx
  exact fun h => hnot (h y hy hre)

end PL1.Daugavet

namespace PL1.Noise

variable (K : Type*) [RCLike K]

/-- Diameter two in every scalar-dual slice of the Schur intrinsic unit ball. -/
theorem schur_intrinsic_diam_realPartSlice
    (φ : (dyadicSystem K schurRates).IntrinsicSpace →L[K] K)
    (hφ : ‖φ‖ = 1) {α : ℝ} (hα : 0 < α) :
    Metric.diam (Daugavet.realPartSlice φ α) = 2 :=
  (schur_intrinsic_sliceCriterion K).diam_realPartSlice φ hφ hα

/-- Diameter two in every scalar-dual slice of the constant-rate intrinsic unit ball. -/
theorem constant_intrinsic_diam_realPartSlice
    (φ : (dyadicSystem K constantRates).IntrinsicSpace →L[K] K)
    (hφ : ‖φ‖ = 1) {α : ℝ} (hα : 0 < α) :
    Metric.diam (Daugavet.realPartSlice φ α) = 2 :=
  (constant_intrinsic_sliceCriterion K).diam_realPartSlice φ hφ hα

/-- The same diameter statement for every real-linear functional, using the
original norm of the Schur intrinsic space. -/
theorem schur_intrinsic_underlyingReal_diam_realPartSlice :
    @Daugavet.SliceDiameterTwo ℝ
      (UnderlyingReal K (dyadicSystem K schurRates).IntrinsicSpace) _
      (inferInstance : NormedAddCommGroup (dyadicSystem K schurRates).IntrinsicSpace)
      (NormedSpace.restrictScalars ℝ K (dyadicSystem K schurRates).IntrinsicSpace) :=
  @Daugavet.SliceCriterion.sliceDiameterTwo ℝ
    (UnderlyingReal K (dyadicSystem K schurRates).IntrinsicSpace) _
    (inferInstance : NormedAddCommGroup (dyadicSystem K schurRates).IntrinsicSpace)
    (NormedSpace.restrictScalars ℝ K (dyadicSystem K schurRates).IntrinsicSpace)
    (schur_intrinsic_underlyingReal_sliceCriterion K)

/-- Diameter two for every real-linear functional on the constant-rate space. -/
theorem constant_intrinsic_underlyingReal_diam_realPartSlice :
    @Daugavet.SliceDiameterTwo ℝ
      (UnderlyingReal K (dyadicSystem K constantRates).IntrinsicSpace) _
      (inferInstance : NormedAddCommGroup (dyadicSystem K constantRates).IntrinsicSpace)
      (NormedSpace.restrictScalars ℝ K (dyadicSystem K constantRates).IntrinsicSpace) :=
  @Daugavet.SliceCriterion.sliceDiameterTwo ℝ
    (UnderlyingReal K (dyadicSystem K constantRates).IntrinsicSpace) _
    (inferInstance : NormedAddCommGroup (dyadicSystem K constantRates).IntrinsicSpace)
    (NormedSpace.restrictScalars ℝ K (dyadicSystem K constantRates).IntrinsicSpace)
    (constant_intrinsic_underlyingReal_sliceCriterion K)

/-- The functional exposing `1` on the Schur intrinsic ball admits maximizing
sequences at asymptotic distance two from that constant. -/
theorem schur_intrinsic_integral_maximizing_sequence_far :
    ∃ y : ℕ → (dyadicSystem K schurRates).IntrinsicSpace,
      (∀ n, ‖y n‖ ≤ 1) ∧
      Tendsto (fun n => RCLike.re (IntrinsicExposedPoint.integralFunctional K schurRates (y n)))
        atTop (𝓝 1) ∧
      Tendsto (fun n => dist (intrinsicCharacter K schurRates ∅) (y n)) atTop (𝓝 2) ∧
      ¬ Tendsto y atTop (𝓝 (intrinsicCharacter K schurRates ∅)) :=
  (schur_intrinsic_sliceCriterion K).exists_maximizing_sequence_far
    (IntrinsicExposedPoint.integralFunctional K schurRates)
    (IntrinsicExposedPoint.norm_integralFunctional K schurRates)
    (intrinsicCharacter K schurRates ∅) (IntrinsicTailNorm.norm_intrinsicConstant K schurRates)

/-- The same explicit failure of strong exposure in the constant-rate space. -/
theorem constant_intrinsic_integral_maximizing_sequence_far :
    ∃ y : ℕ → (dyadicSystem K constantRates).IntrinsicSpace,
      (∀ n, ‖y n‖ ≤ 1) ∧
      Tendsto (fun n => RCLike.re (IntrinsicExposedPoint.integralFunctional K constantRates (y n)))
        atTop (𝓝 1) ∧
      Tendsto (fun n => dist (intrinsicCharacter K constantRates ∅) (y n)) atTop (𝓝 2) ∧
      ¬ Tendsto y atTop (𝓝 (intrinsicCharacter K constantRates ∅)) :=
  (constant_intrinsic_sliceCriterion K).exists_maximizing_sequence_far
    (IntrinsicExposedPoint.integralFunctional K constantRates)
    (IntrinsicExposedPoint.norm_integralFunctional K constantRates)
    (intrinsicCharacter K constantRates ∅) (IntrinsicTailNorm.norm_intrinsicConstant K constantRates)

end PL1.Noise
