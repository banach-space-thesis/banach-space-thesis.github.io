import PEMS.FactorizationSupContractions
import ThesisCommon.Analysis.SequentialCKCZeroRetraction

/-! The sequentially compact C(K) instance of source Theorem 6.5, with
constructed near-isometric subcopy and projection. The quantitative
factorization consequence uses an actual fixed c₀ copy. -/
noncomputable section
open ThesisCommon Set Filter Topology
namespace PEMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeqCompactSpace K]

theorem theorem_6_5_continuousMap
    (V : CZero 𝕜 →L[𝕜] C(K, 𝕜))
    {c ε : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖V x‖) (hε : 0 < ε) :
    ∃ A : CZero 𝕜 →L[𝕜] CZero 𝕜, ∃ R : C(K, 𝕜) →L[𝕜] CZero 𝕜,
      ∃ P : C(K, 𝕜) →L[𝕜] C(K, 𝕜),
        R.comp (V.comp A) = ContinuousLinearMap.id 𝕜 (CZero 𝕜) ∧
        ‖A‖ ≤ 1 ∧ ‖R‖ ≤ (1+ε)/c ∧ ‖V.comp A‖*‖R‖ ≤ 1+ε ∧
        P.comp P = P ∧ ‖P‖ ≤ 1+ε ∧
        Set.range P = Set.range (V.comp A) ∧ Set.range P ⊆ Set.range V :=
  exists_cZero_subcopy_projection_of_sequentiallyCompact V hc hlower hε

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_cZero_factorization_of_fixed_copy_sequentiallyCompact
    (T : E →L[𝕜] C(K, 𝕜)) (V : CZero 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1)
    {c ε : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖T (V x)‖) (hε : 0 < ε) :
    ∃ U : C(K, 𝕜) →L[𝕜] CZero 𝕜, ∃ W : CZero 𝕜 →L[𝕜] E,
      U.comp (T.comp W) = ContinuousLinearMap.id 𝕜 (CZero 𝕜) ∧
      ‖U‖ ≤ (1+ε)/c ∧ ‖W‖ ≤ 1 := by
  obtain ⟨A, U, heq, hA, hU, _⟩ :=
    exists_cZero_almost_contractive_projection_factors (T.comp V) hc hlower hε
  refine ⟨U, V.comp A, ?_, hU, ?_⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using heq
  · exact (V.opNorm_comp_le A).trans
      ((mul_le_mul hV hA (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))

theorem le_factorizationSup_of_fixed_copy_sequentiallyCompact
    (T : E →L[𝕜] C(K, 𝕜)) (V : CZero 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖T (V x)‖) :
    c ≤ factorizationSup (CZero 𝕜) T := by
  letI : NormedAddCommGroup (C(K, 𝕜) →L[𝕜] CZero 𝕜) :=
    ContinuousLinearMap.toNormedAddCommGroup (E := C(K, 𝕜)) (F := CZero 𝕜)
      (σ₁₂ := RingHom.id 𝕜)
  letI : NormedAddCommGroup (CZero 𝕜 →L[𝕜] E) :=
    ContinuousLinearMap.toNormedAddCommGroup (E := CZero 𝕜) (F := E)
      (σ₁₂ := RingHom.id 𝕜)
  letI : Nontrivial (CZero 𝕜) := ⟨⟨cZeroSingle 0 1, 0, by
    intro heq
    have hh := congrArg (fun x : CZero 𝕜 => x 0) heq
    simp at hh⟩⟩
  have hεbound (ε : ℝ) (hε : 0 < ε) : c/(1+ε) ≤ factorizationSup (CZero 𝕜) T := by
    obtain ⟨U, W, hfact, hU, hW⟩ :=
      exists_cZero_factorization_of_fixed_copy_sequentiallyCompact T V hV hc hlower hε
    have hUne : U ≠ 0 := by
      intro hz
      have h := congrArg (fun L : CZero 𝕜 →L[𝕜] CZero 𝕜 => L (cZeroSingle 0 1) 0) hfact
      simp [hz] at h
    have hWne : W ≠ 0 := by
      intro hz
      have h := congrArg (fun L : CZero 𝕜 →L[𝕜] CZero 𝕜 => L (cZeroSingle 0 1) 0) hfact
      simp [hz] at h
    have hUp : 0 < ‖U‖ := norm_pos_iff.mpr hUne
    have hWp : 0 < ‖W‖ := norm_pos_iff.mpr hWne
    have hp : 0 < ‖U‖*‖W‖ := mul_pos hUp hWp
    have hb : ‖U‖*‖W‖ ≤ (1+ε)/c :=
      (mul_le_mul hU hW (norm_nonneg W) (by positivity)).trans_eq (mul_one _)
    have hinv := inv_anti₀ hp hb
    have hconst : c/(1+ε) ≤ ‖U‖⁻¹*‖W‖⁻¹ := by
      simpa only [inv_div, mul_inv_rev, mul_comm] using hinv
    apply hconst.trans
    apply le_csSup
    · refine ⟨‖T‖, ?_⟩
      rintro r (rfl | ⟨U', W', h, rfl⟩)
      · exact norm_nonneg T
      · exact factorization_constant_le_norm T U' W' h
    · exact Or.inr ⟨U, W, hfact, rfl⟩
  have ht : Tendsto (fun ε : ℝ => c/(1+ε)) (𝓝[>] (0:ℝ)) (𝓝 c) := by
    simpa using tendsto_const_nhds.div
      (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)) (by norm_num : (1:ℝ)+0 ≠ 0)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hεbound ε hε

end PEMS


