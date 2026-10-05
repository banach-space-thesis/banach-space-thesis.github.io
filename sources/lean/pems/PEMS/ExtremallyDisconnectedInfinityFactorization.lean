import PEMS.FactorizationSupContractions
import ThesisCommon.Analysis.InfinityFactorizationFromCZero

/-! The countable-coordinate specialization of source Theorem 6.7, via
actual bidual extension and exact infinite support selection. The source
also treats arbitrary infinite index sets; that broader statement is not
asserted here. This specialization gives the sharp ℓ∞ factorization-supremum
consequence needed for extremally disconnected C(K) inputs in Theorem 1.5. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open ThesisCommon
open scoped ENNReal
namespace PEMS
variable {𝕜 : Type} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local instance rosenthalBidualNormedAddCommGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance rosenthalBidualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

theorem theorem_6_7_countable
    (P : StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] E) (hP : ‖P‖ ≤ 1)
    (hPJ : ∀ x, P (NormedSpace.inclusionInDoubleDual 𝕜 E x) = x)
    (T : E →L[𝕜] F) (V : CZero 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖T (V x)‖) :
    ∃ U : F →L[𝕜] EllInfinity 𝕜, ∃ W : EllInfinity 𝕜 →L[𝕜] E,
      U.comp (T.comp W) = ContinuousLinearMap.id 𝕜 (EllInfinity 𝕜) ∧
      ‖U‖ ≤ 1/c ∧ ‖W‖ ≤ 1 := by
  obtain ⟨U, W, heq, hU, hW⟩ :=
    exists_infinity_factorization_of_cZero_bidual_retraction P hP hPJ T V hc hlower
  exact ⟨U, W, heq, hU, hW.trans hV⟩

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
variable [ExtremallyDisconnected K]

theorem le_factorizationSup_infinity_of_fixed_copy_extremallyDisconnected
    (T : C(K, 𝕜) →L[𝕜] F) (V : CZero 𝕜 →L[𝕜] C(K, 𝕜)) (hV : ‖V‖ ≤ 1)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖T (V x)‖) :
    c ≤ factorizationSup (EllInfinity 𝕜) T := by
  letI : Nontrivial (EllInfinity 𝕜) := ⟨⟨lp.single ∞ 0 (1 : 𝕜), 0, by
    intro h
    have hh := congrArg (fun x : EllInfinity 𝕜 => x 0) h
    simp at hh⟩⟩
  letI : NormedAddCommGroup (F →L[𝕜] EllInfinity 𝕜) :=
    ContinuousLinearMap.toNormedAddCommGroup (E := F) (F := EllInfinity 𝕜) (σ₁₂ := RingHom.id 𝕜)
  letI : NormedAddCommGroup (EllInfinity 𝕜 →L[𝕜] C(K, 𝕜)) :=
    ContinuousLinearMap.toNormedAddCommGroup (E := EllInfinity 𝕜) (F := C(K, 𝕜)) (σ₁₂ := RingHom.id 𝕜)
  obtain ⟨U, W, hfact, hU, hW⟩ :=
    exists_infinity_factorization_of_cZero_extremallyDisconnected T V hc hlower
  have hUne : U ≠ 0 := by
    intro hz
    have h := congrArg norm hfact
    simp [hz] at h
  have hWne : W ≠ 0 := by
    intro hz
    have h := congrArg norm hfact
    simp [hz] at h
  have hUn : 0 < ‖U‖ := norm_pos_iff.mpr hUne
  have hWn : 0 < ‖W‖ := norm_pos_iff.mpr hWne
  have hb : ‖U‖*‖W‖ ≤ 1/c :=
    (mul_le_mul hU (hW.trans hV) (norm_nonneg W) (one_div_pos.mpr hc).le).trans_eq (mul_one _)
  have hconst : c ≤ ‖U‖⁻¹*‖W‖⁻¹ := by
    have h := inv_anti₀ (mul_pos hUn hWn) hb
    simpa only [one_div, inv_inv, mul_inv_rev, mul_comm] using h
  apply hconst.trans
  apply le_csSup
  · refine ⟨‖T‖, ?_⟩
    rintro r (rfl | ⟨A, B, h, rfl⟩)
    · exact norm_nonneg T
    · exact factorization_constant_le_norm T A B h
  · exact Or.inr ⟨U, W, hfact, rfl⟩

end PEMS
