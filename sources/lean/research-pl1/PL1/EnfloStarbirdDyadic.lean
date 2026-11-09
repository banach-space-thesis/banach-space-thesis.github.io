import PL1.EnfloStarbirdProjection
import PL1.IntervalDyadicApproximation

/-! # Dyadic verification of the quantitative Enflo–Starbird projection criterion

The operator norm on genuine interval L1 is controlled by its values on dyadic
indicators. Consequently a uniformly small dyadic reconstruction error gives
an actual complemented copy, with an explicit Neumann-series projection.
The disjoint-tree extraction from an arbitrary embedding remains separate.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace PL1.EnfloStarbird
open DyadicTrace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

attribute [local instance] intervalMeasure_probability

private theorem sum_norm_dyadic_pieces_le (n : ℕ) (f : IntervalL1 𝕜) :
    (∑ i ∈ Finset.range (2 ^ n),
      ‖PartitionAverages.coefficient intervalMeasure (cell n) (measurableSet_cell n) i f •
        dyadicVector (𝕜 := 𝕜) n i‖) ≤ ‖f‖ := by
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ n),
        ‖TraceBounds.cellFunctional intervalMeasure (cell n) (measurableSet_cell n) i f‖ :=
      Finset.sum_le_sum (fun i _ => PartitionAverages.norm_coefficient_smul_vector_le
        intervalMeasure (cell n) (measurableSet_cell n) i f)
    _ ≤ ∑ i ∈ Finset.range (2 ^ n),
        ‖L1Masks.mask intervalMeasure (cell n i) (measurableSet_cell n i) f‖ :=
      Finset.sum_le_sum (fun i _ => TraceBounds.norm_cellFunctional_apply_le_mask
        intervalMeasure (cell n) (measurableSet_cell n) i f)
    _ ≤ ‖f‖ := L1Masks.sum_norm_mask_le intervalMeasure _ _ _ (pairwiseDisjoint_cell n) f

/-- It suffices to check the L1 operator bound on all genuine dyadic indicators. -/
theorem opNorm_le_of_dyadic_vectors (T : IntervalL1 𝕜 →L[𝕜] E) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ n i, i < 2 ^ n → ‖T (dyadicVector (𝕜 := 𝕜) n i)‖ ≤
      C * ‖dyadicVector (𝕜 := 𝕜) n i‖) : ‖T‖ ≤ C := by
  have ha (n : ℕ) (f : IntervalL1 𝕜) : ‖T (dyadicAverage n f)‖ ≤ C * ‖f‖ := by
    rw [PartitionAverages.average_apply, map_sum]
    calc
      _ ≤ ∑ i ∈ Finset.range (2 ^ n),
          ‖T (PartitionAverages.coefficient intervalMeasure (cell n) (measurableSet_cell n) i f •
            dyadicVector (𝕜 := 𝕜) n i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (2 ^ n), C *
          ‖PartitionAverages.coefficient intervalMeasure (cell n) (measurableSet_cell n) i f •
            dyadicVector (𝕜 := 𝕜) n i‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [map_smul, norm_smul, norm_smul]
        calc
          _ ≤ ‖PartitionAverages.coefficient (𝕜 := 𝕜) intervalMeasure (cell n)
                (measurableSet_cell n) i f‖ * (C * ‖dyadicVector (𝕜 := 𝕜) n i‖) :=
            mul_le_mul_of_nonneg_left (hT n i (Finset.mem_range.mp hi)) (norm_nonneg _)
          _ = _ := by ring
      _ = C * ∑ i ∈ Finset.range (2 ^ n),
          ‖PartitionAverages.coefficient intervalMeasure (cell n) (measurableSet_cell n) i f •
            dyadicVector (𝕜 := 𝕜) n i‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_left (sum_norm_dyadic_pieces_le n f) hC
  apply ContinuousLinearMap.opNorm_le_bound T hC
  intro f
  exact le_of_tendsto ((T.continuous.tendsto f).comp (dyadicAverage_tendsto f)).norm
    (Filter.Eventually.of_forall (fun n => ha n f))

theorem opNorm_le_iff_dyadic_vectors (T : IntervalL1 𝕜 →L[𝕜] E) (C : ℝ) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ n i, i < 2 ^ n → ‖T (dyadicVector (𝕜 := 𝕜) n i)‖ ≤
      C * ‖dyadicVector (𝕜 := 𝕜) n i‖ := by
  constructor
  · intro h n i _
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  · exact opNorm_le_of_dyadic_vectors T C hC

/-- Dyadic reconstruction errors below one give a complemented copy of actual interval L1. -/
def complementedCopyOfDyadicError (J : IntervalL1 𝕜 →L[𝕜] E)
    (R : E →L[𝕜] IntervalL1 𝕜) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (herror : ∀ n i, i < 2 ^ n →
      ‖dyadicVector (𝕜 := 𝕜) n i - R (J (dyadicVector (𝕜 := 𝕜) n i))‖ ≤
        ε * ‖dyadicVector (𝕜 := 𝕜) n i‖) : ComplementedCopy 𝕜 (IntervalL1 𝕜) E :=
  complementedCopyOfApproximateInverse J R
    ((opNorm_le_of_dyadic_vectors (1 - R.comp J) ε hε herror).trans_lt hε1)

theorem closedComplemented_range_of_dyadicError (J : IntervalL1 𝕜 →L[𝕜] E)
    (R : E →L[𝕜] IntervalL1 𝕜) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (herror : ∀ n i, i < 2 ^ n →
      ‖dyadicVector (𝕜 := 𝕜) n i - R (J (dyadicVector (𝕜 := 𝕜) n i))‖ ≤
        ε * ‖dyadicVector (𝕜 := 𝕜) n i‖) : J.range.ClosedComplemented :=
  (complementedCopyOfDyadicError J R ε hε hε1 herror).closedComplemented_range

#print axioms opNorm_le_iff_dyadic_vectors
#print axioms complementedCopyOfDyadicError

end PL1.EnfloStarbird
