import BanachIsometric.ExactSectionNeighborhood

/-! The existing equivariant chart correction is locally Lipschitz jointly in
the base point and the operator whenever the projection field is Lipschitz. -/

noncomputable section
namespace BanachIsometric.ExactSectionAtlas

open Set Filter
open scoped Topology NNReal

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H) (D : AmbientBodyRetraction S)

omit [FiniteDimensional ℝ E] in
theorem jointCorrection_locallyLipschitz {L : ℝ≥0}
    (hProj : LipschitzWith L (fun a => (H a).starProjection))
    (i : P) (t : P × (E →L[ℝ] F)) (ht : t ∈ Z.correctionChartDomain D i) :
    ∃ W, IsOpen W ∧ t ∈ W ∧ W ⊆ Z.correctionChartDomain D i ∧
      ∃ C : ℝ≥0, LipschitzOnWith C (Z.jointCorrection D i) W := by
  let U := Z.correctionChartDomain D i
  have hU : U ∈ 𝓝 t := (Z.isOpen_correctionChartDomain D hProj.continuous i).mem_nhds ht
  have hFst : LipschitzWith 1 (Prod.fst : P × (E →L[ℝ] F) → P) := LipschitzWith.prod_fst
  have hSnd : LipschitzWith 1 (Prod.snd : P × (E →L[ℝ] F) → (E →L[ℝ] F)) := LipschitzWith.prod_snd
  have hp := hProj.comp hFst
  obtain ⟨V, _CV, hVo, htV, hVU, hV⟩ := exists_lipschitzOnWith_clm_comp_family
    (fun q : P × (E →L[ℝ] F) => (H q.1).starProjection) Prod.snd t hU
    hp.lipschitzOnWith hSnd.lipschitzOnWith
  obtain ⟨CI, hI⟩ := Z.inverse_lipschitz i
  have hIV := hI.comp hFst.lipschitzOnWith (fun q hq => (hVU hq).1)
  obtain ⟨W₀, _CW, hWo, htW, hWV, hW⟩ := exists_lipschitzOnWith_clm_comp_family
    (fun q : P × (E →L[ℝ] F) => Z.inverse i q.1)
    (fun q : P × (E →L[ℝ] F) => (H q.1).starProjection.comp q.2)
    t (hVo.mem_nhds htV) hIV hV
  have hWU := hWV.trans hVU
  have hR := D.lipschitz.comp hW (fun q hq => (hWU hq).2)
  obtain ⟨CF, hF⟩ := Z.forward_lipschitz i
  have hFW := hF.comp hFst.lipschitzOnWith (fun q hq => (hWU hq).1)
  obtain ⟨W, C, hWo', htW', hWW, hLip⟩ := exists_lipschitzOnWith_clm_comp_family
    (fun q : P × (E →L[ℝ] F) => Z.forward i q.1)
    (fun q => D.retract (Z.jointCoordinate i q)) t (hWo.mem_nhds htW) hFW hR
  exact ⟨W, hWo', htW', hWW.trans hWU, C, hLip⟩

include Z D in
theorem exists_locallyLipschitz_fiberwise_neighborhood_retraction {L : ℝ≥0}
    (hProj : LipschitzWith L (fun a => (H a).starProjection)) :
    ∃ U : Set (P × (E →L[ℝ] F)), ∃ r : (P × (E →L[ℝ] F)) → (E →L[ℝ] F),
      IsOpen U ∧
      (∀ t ∈ U, ∃ W, IsOpen W ∧ t ∈ W ∧ W ⊆ U ∧ ∃ C : ℝ≥0, LipschitzOnWith C r W) ∧
      (∀ t : ExactSectionSpace S K H, t.val ∈ U) ∧
      (∀ t ∈ U, Function.Injective (r t) ∧ LinearMap.range (r t).toLinearMap = H t.1 ∧
        r t '' S = K ∩ (H t.1 : Set F)) ∧
      ∀ t : ExactSectionSpace S K H, r t.val = t.val.2 := by
  classical
  let U : Set (P × (E →L[ℝ] F)) := ⋃ i, Z.correctionChartDomain D i
  have hU : IsOpen U := isOpen_iUnion (Z.isOpen_correctionChartDomain D hProj.continuous)
  have hchoose : ∀ t : U, ∃ i, t.val ∈ Z.correctionChartDomain D i :=
    fun t => mem_iUnion.mp t.property
  choose chart hchart using hchoose
  let r : (P × (E →L[ℝ] F)) → (E →L[ℝ] F) := fun t =>
    if ht : t ∈ U then Z.jointCorrection D (chart ⟨t, ht⟩) t else 0
  have hrLocal : ∀ i t, t ∈ Z.correctionChartDomain D i → r t = Z.jointCorrection D i t := by
    intro i t ht
    have htU : t ∈ U := mem_iUnion.mpr ⟨i, ht⟩
    dsimp only [r]
    rw [dif_pos htU]
    exact Z.jointCorrection_eq_on_overlap D _ i t (hchart ⟨t, htU⟩).1 ht.1
  refine ⟨U, r, hU, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    obtain ⟨W, hWo, htW, hWi, C, hC⟩ := Z.jointCorrection_locallyLipschitz D hProj i t hi
    refine ⟨W, hWo, htW, hWi.trans (subset_iUnion _ i), C, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    rw [hrLocal i x (hWi hx), hrLocal i y (hWi hy)]
    exact hC.dist_le_mul x hx y hy
  · intro t
    exact mem_iUnion.mpr ⟨t.val.1,
      Z.exact_operator_mem_correctionChartDomain D t.val.1 t (Z.mem_baseSet t.val.1)⟩
  · intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    rw [hrLocal i t hi]
    exact Z.correctedOperator_valid D (fun a => (H a).starProjection.comp t.2) i t.1 hi.1 hi.2
  · intro t
    have hi := Z.exact_operator_mem_correctionChartDomain D t.val.1 t (Z.mem_baseSet t.val.1)
    rw [hrLocal t.val.1 t.val hi]
    exact Z.jointCorrection_fixes D t.val.1 t (Z.mem_baseSet t.val.1)

end BanachIsometric.ExactSectionAtlas
