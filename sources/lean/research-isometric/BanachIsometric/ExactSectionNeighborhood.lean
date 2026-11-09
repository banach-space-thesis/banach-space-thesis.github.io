import BanachIsometric.ExactSectionCorrection

/-! A genuine fiberwise neighborhood retraction onto the actual exact-section
bundle. The construction is joint in the base point and ambient operator. -/

namespace BanachIsometric

open Set Filter
open scoped Topology NNReal

noncomputable section

namespace ExactSectionAtlas

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H) (D : AmbientBodyRetraction S)

def jointCoordinate (i : P) (t : P × (E →L[ℝ] F)) : E →L[ℝ] E :=
  (Z.inverse i t.1).comp ((H t.1).starProjection.comp t.2)

def jointCorrection (i : P) (t : P × (E →L[ℝ] F)) : E →L[ℝ] F :=
  (Z.forward i t.1).comp (D.retract (Z.jointCoordinate i t))

def correctionChartDomain (i : P) : Set (P × (E →L[ℝ] F)) :=
  {t | t.1 ∈ Z.baseSet i ∧ Z.jointCoordinate i t ∈ D.domain}

omit [FiniteDimensional ℝ E] in
theorem jointCoordinate_continuousAt (hProj : Continuous (fun a => (H a).starProjection))
    (i : P) (t : P × (E →L[ℝ] F)) (ht : t.1 ∈ Z.baseSet i) :
    ContinuousAt (Z.jointCoordinate i) t := by
  obtain ⟨L, hL⟩ := Z.inverse_lipschitz i
  have hB : ContinuousAt (fun t : P × (E →L[ℝ] F) => Z.inverse i t.1) t :=
    (hL.continuousOn.continuousAt ((Z.isOpen_baseSet i).mem_nhds ht)).comp
      (f := Prod.fst) continuous_fst.continuousAt
  have hP : ContinuousAt (fun t : P × (E →L[ℝ] F) => (H t.1).starProjection) t :=
    (hProj.comp continuous_fst).continuousAt
  have hPT : ContinuousAt (fun q : P × (E →L[ℝ] F) =>
      (H q.1).starProjection.comp q.2) t :=
    (ContinuousLinearMap.compL ℝ E F F).continuous₂.continuousAt.comp
      (hP.prodMk continuous_snd.continuousAt)
  exact (ContinuousLinearMap.compL ℝ E F E).continuous₂.continuousAt.comp (hB.prodMk hPT)

omit [FiniteDimensional ℝ E] in
theorem isOpen_correctionChartDomain (hProj : Continuous (fun a => (H a).starProjection))
    (i : P) : IsOpen (Z.correctionChartDomain D i) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  exact inter_mem
    (continuous_fst.continuousAt.preimage_mem_nhds ((Z.isOpen_baseSet i).mem_nhds ht.1))
    ((Z.jointCoordinate_continuousAt hProj i t ht.1).preimage_mem_nhds
      (D.isOpen_domain.mem_nhds ht.2))

omit [FiniteDimensional ℝ E] in
theorem jointCorrection_continuousAt (hProj : Continuous (fun a => (H a).starProjection))
    (i : P) (t : P × (E →L[ℝ] F)) (ht : t ∈ Z.correctionChartDomain D i) :
    ContinuousAt (Z.jointCorrection D i) t := by
  obtain ⟨L, hL⟩ := Z.forward_lipschitz i
  have hA : ContinuousAt (fun t : P × (E →L[ℝ] F) => Z.forward i t.1) t :=
    (hL.continuousOn.continuousAt ((Z.isOpen_baseSet i).mem_nhds ht.1)).comp
      (f := Prod.fst) continuous_fst.continuousAt
  have hR : ContinuousAt (fun t => D.retract (Z.jointCoordinate i t)) t :=
    (D.lipschitz.continuousOn.continuousAt (D.isOpen_domain.mem_nhds ht.2)).comp
      (f := Z.jointCoordinate i) (Z.jointCoordinate_continuousAt hProj i t ht.1)
  exact (ContinuousLinearMap.compL ℝ E E F).continuous₂.continuousAt.comp (hA.prodMk hR)

omit [FiniteDimensional ℝ E] in
theorem jointCorrection_eq_on_overlap (i j : P) (t : P × (E →L[ℝ] F))
    (hi : t.1 ∈ Z.baseSet i) (hj : t.1 ∈ Z.baseSet j) :
    Z.jointCorrection D i t = Z.jointCorrection D j t := by
  exact Z.correctedOperator_eq_on_overlap D (fun a => (H a).starProjection.comp t.2)
    (fun a x => (H a).starProjection_apply_mem (t.2 x)) i j t.1 hi hj

theorem exact_operator_mem_correctionChartDomain (i : P)
    (t : ExactSectionSpace S K H) (hi : t.val.1 ∈ Z.baseSet i) :
    t.val ∈ Z.correctionChartDomain D i := by
  have hProjT : (H t.val.1).starProjection.comp t.val.2 = t.val.2 := by
    apply ContinuousLinearMap.ext
    intro x
    apply (H t.val.1).starProjection_eq_self_iff.mpr
    exact t.property.2.1.le (LinearMap.mem_range_self t.val.2.toLinearMap x)
  refine ⟨hi, ?_⟩
  let g := (Z.actualTrivialization i t).2
  have hg : g.val.val = (Z.inverse i t.val.1).comp t.val.2 :=
    Z.actualTrivialization_snd_val i t hi
  change (Z.inverse i t.val.1).comp ((H t.val.1).starProjection.comp t.val.2) ∈ D.domain
  rw [hProjT, ← hg]
  exact D.contains g

theorem jointCorrection_fixes (i : P) (t : ExactSectionSpace S K H)
    (hi : t.val.1 ∈ Z.baseSet i) : Z.jointCorrection D i t.val = t.val.2 := by
  have hProjT : (H t.val.1).starProjection.comp t.val.2 = t.val.2 := by
    apply ContinuousLinearMap.ext
    intro x
    apply (H t.val.1).starProjection_eq_self_iff.mpr
    exact t.property.2.1.le (LinearMap.mem_range_self t.val.2.toLinearMap x)
  let g := (Z.actualTrivialization i t).2
  have hg : g.val.val = (Z.inverse i t.val.1).comp t.val.2 :=
    Z.actualTrivialization_snd_val i t hi
  change (Z.forward i t.val.1).comp
    (D.retract ((Z.inverse i t.val.1).comp ((H t.val.1).starProjection.comp t.val.2))) = t.val.2
  rw [hProjT, ← hg, D.fixes, hg]
  apply ContinuousLinearMap.ext
  intro x
  exact Z.forward_inverse_apply i t.val.1 hi _
    (t.property.2.1.le (LinearMap.mem_range_self t.val.2.toLinearMap x))

include Z D in
/-- An actual open neighborhood of the exact-map total space has a continuous
fiberwise retraction onto it. The retraction is constructed from the previously
proved body-group retraction and actual atlas; no bundle lifting theorem is
assumed. -/
theorem exists_continuous_fiberwise_neighborhood_retraction
    (hProj : Continuous (fun a => (H a).starProjection)) :
    ∃ U : Set (P × (E →L[ℝ] F)), ∃ r : (P × (E →L[ℝ] F)) → (E →L[ℝ] F),
      IsOpen U ∧ ContinuousOn r U ∧
      (∀ t : ExactSectionSpace S K H, t.val ∈ U) ∧
      (∀ t ∈ U, Function.Injective (r t) ∧ LinearMap.range (r t).toLinearMap = H t.1 ∧
        r t '' S = K ∩ (H t.1 : Set F)) ∧
      ∀ t : ExactSectionSpace S K H, r t.val = t.val.2 := by
  classical
  let U : Set (P × (E →L[ℝ] F)) := ⋃ i, Z.correctionChartDomain D i
  have hU : IsOpen U := isOpen_iUnion (Z.isOpen_correctionChartDomain D hProj)
  have hchoose : ∀ t : U, ∃ i, t.val ∈ Z.correctionChartDomain D i := by
    intro t
    exact mem_iUnion.mp t.property
  choose chart hchart using hchoose
  let r : (P × (E →L[ℝ] F)) → (E →L[ℝ] F) := fun t =>
    if ht : t ∈ U then Z.jointCorrection D (chart ⟨t, ht⟩) t else 0
  have hrLocal : ∀ i t, t ∈ Z.correctionChartDomain D i → r t = Z.jointCorrection D i t := by
    intro i t ht
    have htU : t ∈ U := mem_iUnion.mpr ⟨i, ht⟩
    dsimp only [r]
    rw [dif_pos htU]
    exact Z.jointCorrection_eq_on_overlap D _ i t (hchart ⟨t, htU⟩).1 ht.1
  have hrCont : ContinuousOn r U := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    have hAt := Z.jointCorrection_continuousAt D hProj i t hi
    apply ContinuousAt.continuousWithinAt
    apply hAt.congr_of_eventuallyEq
    filter_upwards [(Z.isOpen_correctionChartDomain D hProj i).mem_nhds hi] with q hq
    exact hrLocal i q hq
  refine ⟨U, r, hU, hrCont, ?_, ?_, ?_⟩
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

end ExactSectionAtlas

end
end BanachIsometric
