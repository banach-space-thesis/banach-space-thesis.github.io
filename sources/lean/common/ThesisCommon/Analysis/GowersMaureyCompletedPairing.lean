import ThesisCommon.Analysis.GowersMaureyCoordinates
import ThesisCommon.Analysis.GowersMaureySupportIntervals

/-! The actual finite coefficient functional on the completed shift space.
This is a finite linear combination of the proved continuous coordinates,
and agrees with the original bilinear finite pairing on the dense space. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def completedPairing (D : ConstructionData 𝕜) :
    C00 𝕜 →ₗ[𝕜] (ShiftSpace D →L[𝕜] 𝕜) :=
  Finsupp.linearCombination 𝕜 (completedCoordinate D)

@[simp] theorem completedPairing_single (D : ConstructionData 𝕜) (i : ℕ) (c : 𝕜) :
    completedPairing D (Finsupp.single i c) = c • completedCoordinate D i := by
  simp [completedPairing]

@[simp] theorem completedPairing_denseEmbedding (D : ConstructionData 𝕜)
    (a : C00 𝕜) (x : PreSpace D) : completedPairing D a (denseEmbedding D x) = pairing a x := by
  classical
  have hpair : pairing a x = ∑ i ∈ a.support, a i * x i := by
    rw [pairing]
    simp only [Finsupp.lsum_apply]
    change (∑ i ∈ x.support, a i * x i) = ∑ i ∈ a.support, a i * x i
    calc
      _ = ∑ i ∈ a.support ∪ x.support, a i * x i := Finset.sum_subset
        Finset.subset_union_right (fun i _ hi => by
          have hz : x i = 0 := Finsupp.notMem_support_iff.mp hi
          exact mul_eq_zero_of_right (a i) hz)
      _ = _ := (Finset.sum_subset Finset.subset_union_left
        (fun i _ hi => by
          have hz : a i = 0 := Finsupp.notMem_support_iff.mp hi
          exact mul_eq_zero_of_left hz (x i))).symm
  rw [hpair]
  simp [completedPairing, Finsupp.linearCombination_apply, Finsupp.sum,
    ContinuousLinearMap.sum_apply, completedCoordinate_denseEmbedding]

theorem completedPairing_norm_bound {D : ConstructionData 𝕜} {a : C00 𝕜}
    (ha : DualUnit (implicitNorm D) a) (x : ShiftSpace D) :
    ‖completedPairing D a x‖ ≤ ‖x‖ := by
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_le (completedPairing D a).continuous.norm continuous_norm
  · intro z
    rw [completedPairing_denseEmbedding, denseEmbedding_norm]
    exact ha z

theorem norm_completedPairing_le_one {D : ConstructionData 𝕜} {a : C00 𝕜}
    (ha : DualUnit (implicitNorm D) a) : ‖completedPairing D a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using completedPairing_norm_bound ha x

end ThesisCommon.GowersMaurey
