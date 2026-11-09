import JFA.CZeroTensor
import JFA.MrowkaTopology
import JFA.ProjectionScalar
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Lemma 4.7 in its uncountable, few-operator context. -/

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
open TopologicalSpace
open scoped ZeroAtInfty
namespace JFA

variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
variable {M : Type*} [MetricSpace M] [CompactSpace M]

private theorem mrowka_czero_nonseparable_of_uncountable
    (h𝒜 : IsAlmostDisjoint 𝒜) (hu : Uncountable 𝒜) :
    ¬ SeparableSpace (MrowkaCZero 𝕜 𝒜) := by
  letI := mrowka_t2Space h𝒜
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  apply czero_nonseparable_of_nonmetrizable
  intro hm
  letI := hm
  letI := mrowka_separableSpace h𝒜
  letI := TopologicalSpace.metrizableSpaceMetric (Mrowka 𝒜)
  exact hu.not_countable mrowka_countable_family_of_secondCountable

/-- The completed operator Q ⊗ I on the actual C₀ product. -/
def compactMrowkaTensorLift (h𝒜 : IsAlmostDisjoint 𝒜) (Q : C(M, 𝕜) →L[𝕜] C(M, 𝕜)) :
    C₀(M × Mrowka 𝒜, 𝕜) →L[𝕜] C₀(M × Mrowka 𝒜, 𝕜) := by
  letI := mrowka_t2Space h𝒜
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  let c := (czeroTensorEquiv (𝕜 := 𝕜) (M := M) (L := Mrowka 𝒜)).toContinuousLinearEquiv
  exact c.toContinuousLinearMap.comp ((injectiveTensorMap Q).comp c.symm.toContinuousLinearMap)

/-- Lemma 4.7. The scalar component of a projection is a projection. -/
theorem lemma_4_7 (h𝒜 : IsAlmostDisjoint 𝒜) (hu : Uncountable 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (P : C₀(M × Mrowka 𝒜, 𝕜) →L[𝕜] C₀(M × Mrowka 𝒜, 𝕜))
    (hP : P.comp P = P) (Q : C(M, 𝕜) →L[𝕜] C(M, 𝕜))
    (S : C₀(M × Mrowka 𝒜, 𝕜) →L[𝕜] C₀(M × Mrowka 𝒜, 𝕜))
    (hS : HasSeparableRange 𝕜 _ _ S) (hPS : P = compactMrowkaTensorLift h𝒜 Q + S) :
    Q.comp Q = Q := by
  letI := mrowka_t2Space h𝒜
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  let c := (czeroTensorEquiv (𝕜 := 𝕜) (M := M) (L := Mrowka 𝒜)).toContinuousLinearEquiv
  let X := MrowkaCZero 𝕜 𝒜
  let E := C(M, 𝕜)
  let P' := c.symm.toContinuousLinearMap.comp (P.comp c.toContinuousLinearMap)
  let S' := c.symm.toContinuousLinearMap.comp (S.comp c.toContinuousLinearMap)
  have hP' : P'.comp P' = P' := by
    apply ContinuousLinearMap.ext
    intro z
    change c.symm (P (c (c.symm (P (c z))))) = c.symm (P (c z))
    rw [c.apply_symm_apply]
    exact congrArg c.symm (DFunLike.congr_fun hP (c z))
  have hS' : HasSeparableRange 𝕜 _ _ S' :=
    (hS.comp_right c.toContinuousLinearMap).comp_left c.symm.toContinuousLinearMap
  have hX : ¬ SeparableSpace X := mrowka_czero_nonseparable_of_uncountable h𝒜 hu
  have hQ : epsilonScalarOperator hX hfew P' = Q := by
    apply epsilonScalarOperator_of_decomposition hX hfew P' Q S' hS'
    intro e x
    let z := injectivePure 𝕜 E X e x
    have hLift : compactMrowkaTensorLift h𝒜 Q (c z) = c (injectiveTensorMap Q z) := by
      change c (injectiveTensorMap Q (c.symm (c z))) = _
      rw [c.symm_apply_apply]
    have he := DFunLike.congr_fun hPS (c z)
    rw [ContinuousLinearMap.add_apply, hLift] at he
    change c.symm (P (c z)) = injectivePure 𝕜 E X (Q e) x + c.symm (S (c z))
    rw [he, map_add, c.symm_apply_apply, injectiveTensorMap_pure]
  simpa only [hQ] using epsilonScalarOperator_projection hX hfew P' hP'

end JFA
