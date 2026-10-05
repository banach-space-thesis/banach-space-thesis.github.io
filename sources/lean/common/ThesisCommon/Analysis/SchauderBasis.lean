import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! Countable Schauder bases, with actual vectors, bounded coordinate
functionals and convergence of the ordered partial sums. No factorisation or
subsequence isomorphism is included among the structure fields.

The unconditional and symmetric norm conditions are expressed on finite
linear combinations. This avoids assuming that a coordinate multiplier or
subsequence map has already been extended to the Banach space.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A normalized Schauder basis indexed starting at zero. -/
structure NormalizedSchauderBasis where
  vector : ℕ → X
  coord : ℕ → X →L[𝕜] 𝕜
  biorthogonal : ∀ i j, coord i (vector j) = if i = j then 1 else 0
  norm_vector : ∀ i, ‖vector i‖ = 1
  expansion : ∀ x : X, Tendsto (fun N => ∑ n ∈ Finset.range N,
    coord n x • vector n) atTop (𝓝 x)

variable {𝕜 X}
namespace NormalizedSchauderBasis
variable (b : NormalizedSchauderBasis 𝕜 X)

/-- Finite coefficient domination with unconditional constant K. For a
complex space the coefficients may have arbitrary complex phases. -/
def UnconditionalWith (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ (F : Finset ℕ) (a c : ℕ → 𝕜),
    (∀ n ∈ F, ‖a n‖ ≤ ‖c n‖) →
    ‖∑ n ∈ F, a n • b.vector n‖ ≤ K * ‖∑ n ∈ F, c n • b.vector n‖

/-- The usual unconditional finite-sum inequality, for some finite constant. -/
def IsUnconditional : Prop := ∃ K : ℝ, b.UnconditionalWith K

/-- The norm makes all coordinatewise scalar contractions contractive. -/
def IsOneUnconditional : Prop := b.UnconditionalWith 1

/-- A symmetric norm: one-unconditionality and invariance of every finite
linear combination under permutations of the basis. -/
def HasSymmetricNorm : Prop := b.IsOneUnconditional ∧
  ∀ (σ : Equiv.Perm ℕ) (F : Finset ℕ) (a : ℕ → 𝕜),
    ‖∑ n ∈ F, a n • b.vector (σ n)‖ = ‖∑ n ∈ F, a n • b.vector n‖

/-- Equivalence to the unit vector basis of ℓ₁, stated as the usual two-sided
finite coefficient inequality. Normalization supplies the upper bound one. -/
def EquivalentEllOne : Prop := ∃ c : ℝ, 0 < c ∧
  ∀ (F : Finset ℕ) (a : ℕ → 𝕜),
    c * ∑ n ∈ F, ‖a n‖ ≤ ‖∑ n ∈ F, a n • b.vector n‖

/-- The actual closed linear span of a subsequence. -/
def subsequenceSpan (f : ℕ → ℕ) : Submodule 𝕜 X :=
  (Submodule.span 𝕜 (Set.range (b.vector ∘ f))).topologicalClosure

theorem finite_sum_norm_le (F : Finset ℕ) (a : ℕ → 𝕜) :
    ‖∑ n ∈ F, a n • b.vector n‖ ≤ ∑ n ∈ F, ‖a n‖ := by
  calc
    _ ≤ ∑ n ∈ F, ‖a n • b.vector n‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, b.norm_vector, mul_one]

theorem coord_finite_sum (F : Finset ℕ) (a : ℕ → 𝕜) (i : ℕ) :
    b.coord i (∑ n ∈ F, a n • b.vector n) = if i ∈ F then a i else 0 := by
  classical
  simp [map_sum, map_smul, b.biorthogonal, Finset.sum_ite_eq]

/-- Coordinates separate points because the partial sums converge. -/
theorem ext {x y : X} (h : ∀ n, b.coord n x = b.coord n y) : x = y := by
  apply tendsto_nhds_unique (b.expansion x)
  simpa only [h] using b.expansion y

/-- The coefficient sequence of each vector tends to zero. -/
theorem coord_tendsto_zero (x : X) :
    Tendsto (fun n => b.coord n x) atTop (𝓝 0) := by
  let s : ℕ → X := fun N => ∑ n ∈ Finset.range N, b.coord n x • b.vector n
  have hs : Tendsto s atTop (𝓝 x) := b.expansion x
  have ht : Tendsto (fun n => b.coord n x • b.vector n) atTop (𝓝 (0 : X)) := by
    have hh := (hs.comp (tendsto_add_atTop_nat 1)).sub hs
    simpa [s, Finset.sum_range_succ] using hh
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_smul, b.norm_vector, mul_one, norm_zero] using ht.norm

/-- For a one-unconditional normalized basis every coordinate functional
has norm at most one, derived from the finite-sum condition. -/
theorem coord_le_norm (h : b.IsOneUnconditional) (n : ℕ) (x : X) :
    ‖b.coord n x‖ ≤ ‖x‖ := by
  classical
  apply ge_of_tendsto (b.expansion x).norm
  filter_upwards [eventually_gt_atTop n] with N hN
  have hn : n ∈ Finset.range N := Finset.mem_range.mpr hN
  have hh := h.2 (Finset.range N) (Pi.single n (b.coord n x)) (fun j => b.coord j x)
    (by
      intro j hj
      by_cases hnj : j = n
      · subst j; simp
      · simp [Pi.single_eq_of_ne hnj])
  simpa [Pi.single_apply, Finset.sum_ite_eq', hn, norm_smul, b.norm_vector] using hh

theorem norm_coord_eq_one (h : b.IsOneUnconditional) (n : ℕ) : ‖b.coord n‖ = 1 := by
  apply le_antisymm
  · apply (b.coord n).opNorm_le_bound (by norm_num)
    intro x
    simpa using b.coord_le_norm h n x
  · have hh := (b.coord n).le_opNorm (b.vector n)
    simpa [b.biorthogonal, b.norm_vector] using hh

/-- Absolute coordinate majorants bound the vector norm, using precisely
the convergent Schauder expansion, not a matrix representation assumption. -/
theorem norm_le_of_coordinate_majorant (x : X) {c : ℕ → ℝ} {C : ℝ}
    (hc : HasSum c C) (hxc : ∀ n, ‖b.coord n x‖ ≤ c n) : ‖x‖ ≤ C := by
  apply le_of_tendsto' (b.expansion x).norm
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖b.coord n x‖ := b.finite_sum_norm_le _ _
    _ ≤ ∑ n ∈ Finset.range N, c n := Finset.sum_le_sum (fun n _ => hxc n)
    _ ≤ C := hc.tsum_eq ▸ hc.summable.sum_le_tsum _
      (fun n _ => (norm_nonneg _).trans (hxc n))

/-- The rank-one argument in Lemma 3.1: vanishing of every matrix row is
equivalent to weak nullity of the normalized basis. This does not yet prove
the separate equivalence with the absence of ℓ₁ subsequence spans. -/
theorem rows_tendsto_zero_iff_weakly_null :
    (∀ (T : X →L[𝕜] X) n, Tendsto (fun m => b.coord n (T (b.vector m)))
      atTop (𝓝 0)) ↔
    (∀ f : X →L[𝕜] 𝕜, Tendsto (fun m => f (b.vector m)) atTop (𝓝 0)) := by
  constructor
  · intro h f
    have hh := h (f.smulRight (b.vector 0)) 0
    simpa [ContinuousLinearMap.smulRight_apply, map_smul, b.biorthogonal] using hh
  · intro h T n
    exact h ((b.coord n).comp T)

end NormalizedSchauderBasis
end ThesisCommon
