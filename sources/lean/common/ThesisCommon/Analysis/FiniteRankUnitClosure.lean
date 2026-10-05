import ThesisCommon.Analysis.FiniteRankUnitPerturbations
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Operators invertible after an actual finite-rank correction form an
open set contained in the closure of the invertible operators. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem sub_finiteRank_mem_closure_units (F : X →L[𝕜] X)
    [FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap)] :
    ContinuousLinearMap.id 𝕜 X-F ∈ closure {U : X →L[𝕜] X | IsUnit U} := by
  obtain ⟨s,hs,hunit⟩ := exists_finite_exceptional_unit_smul_id_sub F
  let f : 𝕜 → X →L[𝕜] X := fun z => z • ContinuousLinearMap.id 𝕜 X-F
  have hf : Continuous f := (continuous_id.smul continuous_const).sub continuous_const
  have hd : Dense sᶜ := hs.countable.dense_compl 𝕜
  have hh := mem_closure_image hf.continuousAt (hd (1 : 𝕜))
  have hi : f '' sᶜ ⊆ {U : X →L[𝕜] X | IsUnit U} := by
    rintro U ⟨z,hz,rfl⟩
    exact hunit z hz
  simpa only [f,one_smul] using (closure_mono hi hh)

def HasFiniteRankInvertibleCorrection (T : X →L[𝕜] X) : Prop :=
  ∃ K : X →L[𝕜] X, FiniteDimensional 𝕜 (LinearMap.range K.toLinearMap) ∧ IsUnit (T+K)

theorem HasFiniteRankInvertibleCorrection.mem_closure_units
    {T : X →L[𝕜] X} (hT : HasFiniteRankInvertibleCorrection T) :
    T ∈ closure {U : X →L[𝕜] X | IsUnit U} := by
  obtain ⟨K,hK,hTK⟩ := hT
  letI := hK
  let u := hTK.unit
  let F : X →L[𝕜] X := (↑u⁻¹ : X →L[𝕜] X)*K
  have hF : FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) := by
    change FiniteDimensional 𝕜 (LinearMap.range
      (((↑u⁻¹ : X →L[𝕜] X).comp K).toLinearMap))
    rw [ContinuousLinearMap.coe_comp, LinearMap.range_comp]
    infer_instance
  letI := hF
  have hh := sub_finiteRank_mem_closure_units F
  have hc : Continuous (fun V : X →L[𝕜] X => (↑u : X →L[𝕜] X)*V) :=
    continuous_const.mul continuous_id
  have himage := mem_closure_image hc.continuousAt hh
  have hsubset : (fun V : X →L[𝕜] X => (↑u : X →L[𝕜] X)*V) ''
      {V : X →L[𝕜] X | IsUnit V} ⊆ {V : X →L[𝕜] X | IsUnit V} := by
    rintro V ⟨W,hW,rfl⟩
    exact u.isUnit.mul hW
  have he : (↑u : X →L[𝕜] X)*(ContinuousLinearMap.id 𝕜 X-F) = T := by
    change (↑u : X →L[𝕜] X)*(1-(↑u⁻¹ : X →L[𝕜] X)*K) = T
    rw [mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
    change (T+K)-K = T
    exact add_sub_cancel_right T K
  rw [he] at himage
  exact closure_mono hsubset himage

theorem isOpen_hasFiniteRankInvertibleCorrection :
    IsOpen {T : X →L[𝕜] X | HasFiniteRankInvertibleCorrection T} := by
  rw [isOpen_iff_mem_nhds]
  intro T hT
  obtain ⟨K,hK,hTK⟩ := hT
  have hnhds : {U : X →L[𝕜] X | IsUnit (U+K)} ∈ 𝓝 T :=
    (Units.isOpen.preimage (continuous_id.add continuous_const)).mem_nhds hTK
  apply Filter.mem_of_superset hnhds
  intro U hU
  exact ⟨K,hK,hU⟩

omit [CompleteSpace X] in
theorem hasFiniteRankInvertibleCorrection_of_isUnit
    {T : X →L[𝕜] X} (hT : IsUnit T) : HasFiniteRankInvertibleCorrection T := by
  refine ⟨0,?_,by simpa using hT⟩
  change FiniteDimensional 𝕜 (LinearMap.range (0 : X →ₗ[𝕜] X))
  rw [LinearMap.range_zero]
  infer_instance

end ThesisCommon
