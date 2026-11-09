import Mathlib.Analysis.Calculus.FDeriv.Mul
import BanachIsometric.LocalIsometricFrames

/-!
# Local operator Lipschitz bounds for inversion and composition

These estimates allow a normalized exact family to be conjugated back to the
original bodies. Inversion uses its proved strict derivative at a unit;
composition uses bounds on a smaller neighbourhood of the parameter.
-/

namespace BanachIsometric

open Set Filter
open scoped Topology NNReal

section InverseAlgebra

variable {P A : Type*} [PseudoMetricSpace P] [NormedRing A]
  [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exists_lipschitzOnWith_ringInverse_family
    (f : P → A) (a₀ : P) {U : Set P} (hU : U ∈ 𝓝 a₀)
    {L : ℝ≥0} (hLip : LipschitzOnWith L f U) (hunit : IsUnit (f a₀)) :
    ∃ W : Set P, ∃ K : ℝ≥0, IsOpen W ∧ a₀ ∈ W ∧ W ⊆ U ∧
      LipschitzOnWith K (fun a ↦ Ring.inverse (f a)) W := by
  have hcont : ContinuousAt f a₀ := hLip.continuousOn.continuousAt hU
  have hInv := hasStrictFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit
  obtain ⟨KI, V, hV, hILip⟩ := hInv.exists_lipschitzOnWith
  have hV' : V ∈ 𝓝 (f a₀) := by simpa only [hunit.unit_spec] using hV
  have hpre : f ⁻¹' V ∈ 𝓝 a₀ := hcont.preimage_mem_nhds hV'
  obtain ⟨W, hWsub, hWopen, ha₀W⟩ := mem_nhds_iff.mp (inter_mem hU hpre)
  refine ⟨W, KI * L, hWopen, ha₀W, hWsub.trans inter_subset_left, ?_⟩
  exact hILip.comp (hLip.mono (hWsub.trans inter_subset_left)) (fun a ha ↦ (hWsub ha).2)

end InverseAlgebra

section InverseEquivalences

variable {P E : Type*} [PseudoMetricSpace P] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_lipschitzOnWith_symm_continuousLinearEquiv_family
    (e : P → E ≃L[ℝ] E) (a₀ : P) {U : Set P} (hU : U ∈ 𝓝 a₀)
    {L : ℝ≥0} (hLip : LipschitzOnWith L (fun a ↦ (e a).toContinuousLinearMap) U) :
    ∃ W : Set P, ∃ K : ℝ≥0, IsOpen W ∧ a₀ ∈ W ∧ W ⊆ U ∧
      LipschitzOnWith K (fun a ↦ (e a).symm.toContinuousLinearMap) W := by
  have hunit : IsUnit (e a₀).toContinuousLinearMap := ⟨(e a₀).toUnit, rfl⟩
  obtain ⟨W, K, hW, ha₀W, hWU, hInv⟩ :=
    exists_lipschitzOnWith_ringInverse_family (fun a ↦ (e a).toContinuousLinearMap)
      a₀ hU hLip hunit
  refine ⟨W, K, hW, ha₀W, hWU, ?_⟩
  simpa only [ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv] using hInv

end InverseEquivalences

section Composition

variable {P E F G : Type*} [PseudoMetricSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_lipschitzOnWith_clm_comp_family
    (A : P → F →L[ℝ] G) (B : P → E →L[ℝ] F) (a₀ : P)
    {U : Set P} (hU : U ∈ 𝓝 a₀) {KA KB : ℝ≥0}
    (hA : LipschitzOnWith KA A U) (hB : LipschitzOnWith KB B U) :
    ∃ W : Set P, ∃ K : ℝ≥0, IsOpen W ∧ a₀ ∈ W ∧ W ⊆ U ∧
      LipschitzOnWith K (fun a ↦ (A a).comp (B a)) W := by
  have hAc : ContinuousAt A a₀ := hA.continuousOn.continuousAt hU
  have hBc : ContinuousAt B a₀ := hB.continuousOn.continuousAt hU
  have hAball : A ⁻¹' Metric.ball (A a₀) 1 ∈ 𝓝 a₀ :=
    hAc.preimage_mem_nhds (Metric.ball_mem_nhds _ zero_lt_one)
  have hBball : B ⁻¹' Metric.ball (B a₀) 1 ∈ 𝓝 a₀ :=
    hBc.preimage_mem_nhds (Metric.ball_mem_nhds _ zero_lt_one)
  obtain ⟨W, hWsub, hWopen, ha₀W⟩ := mem_nhds_iff.mp (inter_mem hU (inter_mem hAball hBball))
  have hWU : W ⊆ U := hWsub.trans inter_subset_left
  refine ⟨W, (‖A a₀‖₊ + 1) * KB + KA * (‖B a₀‖₊ + 1), hWopen, ha₀W, hWU, ?_⟩
  apply lipschitzOnWith_clm_comp (hA.mono hWU) (hB.mono hWU)
  · intro a ha
    change ‖A a‖ ≤ ‖A a₀‖ + 1
    exact norm_le_norm_add_const_of_dist_le (show dist (A a) (A a₀) < 1 from (hWsub ha).2.1).le
  · intro a ha
    change ‖B a‖ ≤ ‖B a₀‖ + 1
    exact norm_le_norm_add_const_of_dist_le (show dist (B a) (B a₀) < 1 from (hWsub ha).2.2).le

end Composition

end BanachIsometric
