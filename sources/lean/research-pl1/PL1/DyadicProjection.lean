import PL1.IntrinsicGraph
import PL1.L1Sum
import PL1.ResolventEstimates
import PL1.WeakSchur

/-!
# The projection constructed from a dyadic resolvent system

The operator hypotheses are the precise conclusions required from the
resolvent construction. Under these hypotheses we construct the intrinsic
Banach space as a closed graph in the actual countable ell1 sum, its
reconstruction map, and the projection. This conditional construction does
not assert that either of the paper's measure-theoretic resolvent families
has yet been constructed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace PL1

open ResolventEstimates

/-- The analytic properties of the dyadic resolvents used in the construction. -/
structure DyadicSystem (𝕜 Y : Type*) [RCLike 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  operator : ℕ → Y →L[𝕜] Y
  contractive : ∀ n, ‖operator n‖ ≤ 1
  commute : ∀ i j, (operator i).comp (operator j) = (operator j).comp (operator i)
  resolvent : ∀ i j, (ContinuousLinearMap.id 𝕜 Y - operator i).comp (operator j) =
    (((dyadicRatio ^ 2) ^ i / (dyadicRatio ^ 2) ^ j : ℝ) : 𝕜) •
      (operator i).comp (ContinuousLinearMap.id 𝕜 Y - operator j)
  strong : ∀ y, Tendsto (fun n => operator n y) atTop (𝓝 y)

namespace DyadicSystem

variable {𝕜 Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

variable (S : DyadicSystem 𝕜 Y)

/-- The weighted defect operators that define the intrinsic norm. -/
abbrev analysis := analysisCoordinate S.operator

/-- The unweighted underlying reconstruction columns. -/
abbrev baseColumn := synthesisCoordinate S.operator

/-- The actual intrinsic graph normed space. -/
abbrev IntrinsicSpace := IntrinsicGraph.Space S.analysis

/-- Its isometric embedding into the actual countable ell1 sum. -/
abbrev inclusion : S.IntrinsicSpace →ₗᵢ[𝕜] L1Sum Y :=
  IntrinsicGraph.inclusion S.analysis

/-- A reconstruction column, with its codomain equipped with the intrinsic norm. -/
def column (j : ℕ) : Y →L[𝕜] S.IntrinsicSpace :=
  IntrinsicGraph.column S.analysis rfl (S.baseColumn j)
    (weighted_column_apply_norm_summable S.operator S.contractive S.resolvent j)
    projectionBound
    (weighted_column_apply_norm_tsum_le S.operator S.contractive S.resolvent j)

theorem projectionBound_nonneg : 0 ≤ projectionBound := by
  unfold projectionBound
  positivity

theorem norm_column_le (j : ℕ) : ‖S.column j‖ ≤ projectionBound :=
  IntrinsicGraph.norm_column_le _ _ _ _ _ _ projectionBound_nonneg

@[simp]
theorem evalZero_column (j : ℕ) (y : Y) :
    IntrinsicGraph.evalZero S.analysis (S.column j y) = S.baseColumn j y :=
  IntrinsicGraph.evalZero_column _ _ _ _ _ _ _

@[simp]
theorem coord_column (i j : ℕ) (y : Y) :
    IntrinsicGraph.coord S.analysis i (S.column j y) = S.analysis i (S.baseColumn j y) := rfl

variable [CompleteSpace Y]

/-- The bounded map K from the ambient ell1 sum to the intrinsic Banach space. -/
def reconstruction : L1Sum Y →L[𝕜] S.IntrinsicSpace :=
  L1Sum.synthesis S.column projectionBound S.norm_column_le

theorem norm_reconstruction_le : ‖S.reconstruction‖ ≤ projectionBound :=
  L1Sum.norm_synthesis_le _ _ _ projectionBound_nonneg

@[simp]
theorem reconstruction_apply (x : L1Sum Y) :
    S.reconstruction x = ∑' j, S.column j (x j) := rfl

@[simp]
theorem reconstruction_single (j : ℕ) (y : Y) :
    S.reconstruction (lp.single 1 j y) = S.column j y :=
  L1Sum.synthesis_single _ _ _ _ _

/-- The underlying Y-valued reconstruction series is the formula in the paper. -/
theorem evalZero_reconstruction (x : L1Sum Y) :
    IntrinsicGraph.evalZero S.analysis (S.reconstruction x) =
      ∑' j, S.baseColumn j (x j) := by
  rw [reconstruction_apply,
    (IntrinsicGraph.evalZero S.analysis).map_tsum
      (L1Sum.summable_columns S.column projectionBound S.norm_column_le x)]
  simp only [evalZero_column]

/-- The candidate matrix projection is J composed with K. -/
def projection : L1Sum Y →L[𝕜] L1Sum Y :=
  S.inclusion.toContinuousLinearMap.comp S.reconstruction

theorem norm_projection_le : ‖S.projection‖ ≤ projectionBound := by
  apply ContinuousLinearMap.opNorm_le_bound _ projectionBound_nonneg
  intro x
  change ‖S.inclusion (S.reconstruction x)‖ ≤ projectionBound * ‖x‖
  rw [S.inclusion.norm_map]
  exact S.reconstruction.le_opNorm x |>.trans
    (mul_le_mul_of_nonneg_right S.norm_reconstruction_le (norm_nonneg _))

/-- Every matrix block is exactly the weighted resolvent formula. -/
theorem projection_single_coord (i j : ℕ) (y : Y) :
    S.projection (lp.single 1 j y) i = S.analysis i (S.baseColumn j y) := by
  change IntrinsicGraph.coord S.analysis i
    (S.reconstruction (lp.single 1 j y)) = _
  rw [reconstruction_single, coord_column]

/-- The zeroth matrix block is S0, the resolvent at time one. -/
theorem projection_zero_zero (y : Y) :
    S.projection (lp.single 1 0 y) 0 = S.operator 0 y := by
  rw [projection_single_coord]
  rfl

/-- Absolute convergence permits reconstruction, and the finite sums telescope
to the strongly convergent dyadic resolvents. Thus KJ is the identity. -/
theorem reconstruction_inclusion (x : S.IntrinsicSpace) :
    S.reconstruction (S.inclusion x) = x := by
  apply IntrinsicGraph.evalZero_injective S.analysis
  rw [evalZero_reconstruction]
  have hs := L1Sum.summable_columns S.baseColumn 1
    (synthesisCoordinate_norm_le_one S.operator S.contractive) (S.inclusion x)
  have ht := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have heq (N : ℕ) :
      (∑ j ∈ Finset.range (N + 1), S.baseColumn j (S.inclusion x j)) =
        S.operator N (IntrinsicGraph.evalZero S.analysis x) := by
    calc
      _ = ∑ j ∈ Finset.range (N + 1),
          S.baseColumn j (S.analysis j (IntrinsicGraph.evalZero S.analysis x)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [show S.inclusion x j =
              S.analysis j (IntrinsicGraph.evalZero S.analysis x) from x.property j]
      _ = _ := weighted_composition_partial_sum_apply
        S.operator S.commute S.resolvent N _
  have ht' : Tendsto
      (fun N => S.operator N (IntrinsicGraph.evalZero S.analysis x)) atTop
      (𝓝 (∑' j, S.baseColumn j (S.inclusion x j))) := by
    change Tendsto (fun N => ∑ j ∈ Finset.range (N + 1),
      S.baseColumn j (S.inclusion x j)) atTop _ at ht
    simpa only [heq] using ht
  exact tendsto_nhds_unique ht' (S.strong _)

theorem reconstruction_comp_inclusion :
    S.reconstruction.comp S.inclusion.toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 S.IntrinsicSpace := by
  apply ContinuousLinearMap.ext
  intro x
  exact S.reconstruction_inclusion x

theorem reconstruction_surjective : Function.Surjective S.reconstruction :=
  fun x => ⟨S.inclusion x, S.reconstruction_inclusion x⟩

/-- The constructed operator is an actual bounded projection. -/
theorem isProjection : IsProjection S.projection := by
  apply ContinuousLinearMap.ext
  intro x
  change S.inclusion (S.reconstruction (S.inclusion (S.reconstruction x))) =
    S.inclusion (S.reconstruction x)
  rw [reconstruction_inclusion]

/-- Its range is precisely the intrinsic graph, with the inherited ell1 norm. -/
theorem projection_range : S.projection.range = IntrinsicGraph.graph S.analysis := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (S.reconstruction y).property
  · intro hx
    refine ⟨x, ?_⟩
    change S.inclusion (S.reconstruction (S.inclusion ⟨x, hx⟩)) = x
    rw [reconstruction_inclusion]
    rfl

theorem isClosed_projection_range : IsClosed (S.projection.range : Set (L1Sum Y)) :=
  S.isProjection.isClosed_range

/-- The quantitative operator conclusion of Proposition 4.2, conditional only
on the stated analytic properties of the dyadic resolvents. -/
theorem projection_spec :
    IsProjection S.projection ∧ ‖S.projection‖ ≤ projectionBound ∧
      S.projection.range = IntrinsicGraph.graph S.analysis ∧
      IsClosed (S.projection.range : Set (L1Sum Y)) ∧
      (∀ y, S.projection (lp.single 1 0 y) 0 = S.operator 0 y) :=
  ⟨S.isProjection, S.norm_projection_le, S.projection_range,
    S.isClosed_projection_range, S.projection_zero_zero⟩

end DyadicSystem
end PL1
