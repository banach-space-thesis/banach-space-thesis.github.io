import ThesisCommon.Analysis.JamesProjectionSampling
import ThesisCommon.Analysis.JamesProjectionDichotomy
import ThesisCommon.Analysis.JamesSamplingKernelBlocks
import ThesisCommon.Analysis.JamesBlockFiniteSections
import ThesisCommon.Analysis.ProjectionSamplingDecomposition
import ThesisCommon.Analysis.JamesRepeatedFiniteAbsorption

/-! Primariness from the actual sampling factorization. The remaining
projection summand is a bounded retract of a genuine finite James block sum;
the proved repeated finite-section absorption removes that summand. This
does not assume a classification of reflexive subspaces of James space. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
private theorem composed_retractions_through_equiv
    {𝕜 Z K L F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    [NormedAddCommGroup L] [NormedSpace 𝕜 L]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (J : Z →L[𝕜] K) (Q : K →L[𝕜] Z) (I : K →L[𝕜] L) (B : L →L[𝕜] K)
    (eL : L ≃L[𝕜] F) (hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 Z)
    (hBI : B.comp I = ContinuousLinearMap.id 𝕜 K) :
    (Q.comp (B.comp eL.symm.toContinuousLinearMap)).comp
      (eL.toContinuousLinearMap.comp (I.comp J)) = ContinuousLinearMap.id 𝕜 Z := by
  ext z
  change Q (B (eL.symm (eL (I (J z))))) = z
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have h := DFunLike.congr_fun hBI (J z)
  change B (I (J z)) = J z at h
  rw [h]
  exact DFunLike.congr_fun hQJ z

variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (hpl : 1 < p.val.toReal)
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

theorem james_projection_range_isomorphic_of_sampling
    (P : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) (hP : P.comp P = P)
    (α : ℕ → ℕ) (hα : StrictMono α)
    (V : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (E : JamesSequenceSpace 𝕜 p ≃L[𝕜] JamesSequenceSpace 𝕜 p)
    (hf : (E.toContinuousLinearMap.comp (jamesSample (𝕜 := 𝕜) p hp α hα)).comp
      (P.comp V) = ContinuousLinearMap.id 𝕜 _) :
    Nonempty (JamesSequenceSpace 𝕜 p ≃L[𝕜] LinearMap.range P.toLinearMap) := by
  obtain ⟨R, ⟨e⟩, J, Q, hQJ⟩ := projection_range_sampling_decomposition P
    (jamesSample (𝕜 := 𝕜) p hp α hα) V hP E hf
  let I := jamesSamplingKernelBlockInsert (𝕜 := 𝕜) p hp α hα
  let B := jamesSamplingKernelBlockRead (𝕜 := 𝕜) p hp α hα
  let eL := jamesBlockFiniteSectionEquiv (𝕜 := 𝕜) p hp (jamesSamplingEndpoints α)
    (jamesSamplingEndpoints_strict α hα) rfl
  let j := eL.toContinuousLinearMap.comp (I.comp J)
  let q := Q.comp (B.comp eL.symm.toContinuousLinearMap)
  have hqj : q.comp j = ContinuousLinearMap.id 𝕜 _ :=
    composed_retractions_through_equiv J Q I B eL hQJ
      (jamesSamplingKernelBlockRead_comp_insert (𝕜 := 𝕜) p hp α hα)
  exact ⟨(jamesAbsorbRetractOfFiniteSectionSum (𝕜 := 𝕜) p hp
    (jamesBlockLengths (jamesSamplingEndpoints α)) j q hqj).trans e.symm⟩

include hp hpl in
theorem james_nonweaklyCompact_projection_range_isomorphic
    (P : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (hP : P.comp P = P) (hnot : ¬ IsWeaklyCompactOperator P) :
    Nonempty (JamesSequenceSpace 𝕜 p ≃L[𝕜] LinearMap.range P.toLinearMap) := by
  obtain ⟨α, hα, V, E, hf, _, _⟩ :=
    james_nonweaklyCompact_projection_sampling_split p hp hpl P hP hnot
  exact james_projection_range_isomorphic_of_sampling p hp P hP α hα V E hf

include hp hpl in
theorem jamesSequence_primary : IsPrimary 𝕜 (JamesSequenceSpace 𝕜 p) := by
  intro P hP
  by_cases h : IsWeaklyCompactOperator P
  · apply Or.inr
    apply james_nonweaklyCompact_projection_range_isomorphic p hp hpl _
      (complementary_projection hP)
    exact (james_projection_weaklyCompact_iff_complement_not p hp hpl P hP).mp h
  · exact Or.inl (james_nonweaklyCompact_projection_range_isomorphic p hp hpl P hP h)

end ThesisCommon
