import LindenstraussRetraction.SchauderBasis
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Basic identities for the sequential Schauder basis

These lemmas justify the partial-sum projection interpretation and the
equivalence of the prefix/tail and interval conventions for bimonotonicity.
-/

noncomputable section

open scoped BigOperators
open Filter Topology

namespace LindenstraussRetraction.SchauderBasis

universe u v

variable {𝕜 : Type v} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : SchauderBasis 𝕜 X)

@[simp] theorem coord_vector (n m : ℕ) :
    b.coord n (b.vector m) = if n = m then 1 else 0 := b.biorthogonal n m

@[simp] theorem partialSum_apply (N : ℕ) (x : X) :
    b.partialSum N x = ∑ n ∈ Finset.range N, b.coord n x • b.vector n := by
  simp [partialSum]

@[simp] theorem partialSum_zero : b.partialSum 0 = 0 := by
  simp [partialSum]

@[simp] theorem partialSum_vector (N m : ℕ) :
    b.partialSum N (b.vector m) = if m < N then b.vector m else 0 := by
  simp [partialSum_apply, coord_vector]

@[simp] theorem coord_partialSum (N m : ℕ) (x : X) :
    b.coord m (b.partialSum N x) = if m < N then b.coord m x else 0 := by
  simp [partialSum_apply, map_sum, coord_vector]

theorem partialSum_comp_of_le_left {N M : ℕ} (h : N ≤ M) :
    (b.partialSum N).comp (b.partialSum M) = b.partialSum N := by
  ext x
  change b.partialSum N (b.partialSum M x) = b.partialSum N x
  conv_lhs => rw [partialSum_apply]
  conv_rhs => rw [partialSum_apply]
  simp only [coord_partialSum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [if_pos (lt_of_lt_of_le (Finset.mem_range.mp hn) h)]

theorem partialSum_comp_of_le_right {N M : ℕ} (h : M ≤ N) :
    (b.partialSum N).comp (b.partialSum M) = b.partialSum M := by
  ext x
  change b.partialSum N (b.partialSum M x) = b.partialSum M x
  rw [b.partialSum_apply M x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [partialSum_vector, if_pos (lt_of_lt_of_le (Finset.mem_range.mp hm) h)]

@[simp] theorem partialSum_comp (N M : ℕ) :
    (b.partialSum N).comp (b.partialSum M) = b.partialSum (min N M) := by
  rcases le_total N M with h | h
  · rw [min_eq_left h]
    exact b.partialSum_comp_of_le_left h
  · rw [min_eq_right h]
    exact b.partialSum_comp_of_le_right h

theorem tendsto_partialSum (x : X) :
    Tendsto (fun N => b.partialSum N x) atTop (𝓝 x) := by
  simpa only [partialSum_apply] using b.expansion x

/-- A consecutive interval projection is a prefix composed with a tail. -/
theorem interval_eq_comp {M N : ℕ} (h : M ≤ N) :
    b.partialSum N - b.partialSum M =
      (b.partialSum N).comp (ContinuousLinearMap.id 𝕜 X - b.partialSum M) := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
    b.partialSum_comp_of_le_right h]

/-- The paper's prefix/tail convention makes every consecutive interval
projection contractive. -/
theorem interval_contractive (hb : b.IsBimonotone) {M N : ℕ} (h : M ≤ N) :
    ‖b.partialSum N - b.partialSum M‖ ≤ 1 := by
  rw [b.interval_eq_comp h]
  calc
    ‖(b.partialSum N).comp (ContinuousLinearMap.id 𝕜 X - b.partialSum M)‖ ≤
        ‖b.partialSum N‖ * ‖ContinuousLinearMap.id 𝕜 X - b.partialSum M‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (hb.1 N) (hb.2 M) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-- Bimonotonicity is equivalently contractivity of every consecutive interval
projection. The tail estimate follows by taking the pointwise limit of the
finite intervals. -/
theorem isBimonotone_iff_interval_contractive :
    b.IsBimonotone ↔ ∀ M N : ℕ, M ≤ N → ‖b.partialSum N - b.partialSum M‖ ≤ 1 := by
  constructor
  · intro hb M N h
    exact b.interval_contractive hb h
  · intro h
    constructor
    · intro N
      simpa only [partialSum_zero, sub_zero] using h 0 N (Nat.zero_le N)
    · intro M
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, one_mul]
      apply le_of_tendsto (((b.tendsto_partialSum x).sub tendsto_const_nhds).norm)
      filter_upwards [eventually_ge_atTop M] with N hMN
      calc
        ‖b.partialSum N x - b.partialSum M x‖ =
            ‖(b.partialSum N - b.partialSum M) x‖ := rfl
        _ ≤ ‖b.partialSum N - b.partialSum M‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ x
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (h M N hMN) (norm_nonneg x)
        _ = ‖x‖ := one_mul _

/-- The continuous coordinate functionals recover the coefficients of every
convergent ordered expansion. Thus the structure encodes the usual uniqueness
condition for a Schauder basis. -/
theorem coefficients_unique (a : ℕ → 𝕜) (x : X)
    (ha : Tendsto (fun N => ∑ n ∈ Finset.range N, a n • b.vector n) atTop (𝓝 x))
    (m : ℕ) : a m = b.coord m x := by
  have ht : Tendsto
      (fun N => b.coord m (∑ n ∈ Finset.range N, a n • b.vector n))
      atTop (𝓝 (b.coord m x)) := (b.coord m).continuous.continuousAt.tendsto.comp ha
  have hc : Tendsto
      (fun N => b.coord m (∑ n ∈ Finset.range N, a n • b.vector n))
      atTop (𝓝 (a m)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop m] with N hN
    simp [map_sum, coord_vector, hN]
  exact tendsto_nhds_unique hc ht

end LindenstraussRetraction.SchauderBasis
