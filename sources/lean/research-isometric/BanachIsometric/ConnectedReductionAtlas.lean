import BanachIsometric.AssociatedComponentProjection

/-! An actual section of the component covering refines the original atlas
so its adjusted transition functions lie in the connected identity component.
The refinement is open because the component quotient is discrete. -/

noncomputable section

namespace BanachIsometric.ExactSectionAtlas

open Set Bundle
open scoped Topology
attribute [local instance] BanachIsometric.connectedComponentOfOne_normal

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : BanachIsometric.ExactSectionAtlas S K H)
    (s : C(P, Z.componentCore.TotalSpace)) (hs : ∀ a, Z.componentCore.proj (s a) = a)

def componentChartValue (i a : P) : ComponentGroup (S := S) :=
  (Z.componentCore.localTriv i (s a)).2

include hs in
theorem continuousOn_componentChartValue (i : P) :
    ContinuousOn (Z.componentChartValue s i) (Z.baseSet i) := by
  apply continuous_snd.comp_continuousOn
  exact (Z.componentCore.localTriv i).continuousOn_toFun.comp s.continuous.continuousOn
    (fun a ha => by change Z.componentCore.proj (s a) ∈ Z.baseSet i; rwa [hs a])

def reducedBaseSet (i : P) : Set P := Z.baseSet i ∩
  (Z.componentChartValue s i) ⁻¹' {Z.componentChartValue s i i}

include hs in
theorem isOpen_reducedBaseSet
    (hopen : IsOpen (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) :
      Set (bodyAutomorphismGroup S))) (i : P) : IsOpen (Z.reducedBaseSet s i) := by
  letI : DiscreteTopology (ComponentGroup (S := S)) := Subgroup.discreteTopology _ hopen
  exact (Z.continuousOn_componentChartValue s hs i).isOpen_inter_preimage
    (Z.isOpen_baseSet i) (isOpen_discrete _)

theorem mem_reducedBaseSet (i : P) : i ∈ Z.reducedBaseSet s i :=
  ⟨Z.mem_baseSet i, rfl⟩

def componentRepresentative (i : P) : bodyAutomorphismGroup S :=
  (QuotientGroup.mk_surjective (Z.componentChartValue s i i)).choose

theorem componentRepresentative_class (i : P) :
    (QuotientGroup.mk (Z.componentRepresentative s i) : ComponentGroup (S := S)) =
      Z.componentChartValue s i i :=
  (QuotientGroup.mk_surjective (Z.componentChartValue s i i)).choose_spec

include hs in
theorem componentChartValue_transition (i j a : P)
    (hi : a ∈ Z.baseSet i) (hj : a ∈ Z.baseSet j) :
    Z.componentChartValue s j a =
      QuotientGroup.mk (Z.transition i j a) * Z.componentChartValue s i a := by
  have hbase : (s a).1 = a := hs a
  have hT : Z.transition i j a * Z.transition (s a).1 i (s a).1 =
      Z.transition (s a).1 j (s a).1 := by
    rw [hbase]
    exact Z.transition_cocycle a i j a (Z.mem_baseSet a) hi hj
  change QuotientGroup.mk (Z.transition (s a).1 j (s a).1) *
      (show ComponentGroup (S := S) from (s a).2) =
    QuotientGroup.mk (Z.transition i j a) *
      (QuotientGroup.mk (Z.transition (s a).1 i (s a).1) *
        (show ComponentGroup (S := S) from (s a).2))
  rw [← mul_assoc, ← QuotientGroup.mk_mul, hT]

include hs in
theorem reducedTransition_mem (i j a : P)
    (ha : a ∈ Z.reducedBaseSet s i ∩ Z.reducedBaseSet s j) :
    (Z.componentRepresentative s j)⁻¹ * Z.transition i j a * Z.componentRepresentative s i ∈
      Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) := by
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk ((Z.componentRepresentative s j)⁻¹ * Z.transition i j a *
    Z.componentRepresentative s i) : ComponentGroup (S := S)) = 1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    Z.componentRepresentative_class s i, Z.componentRepresentative_class s j,
    mul_assoc]
  have hqi : Z.componentChartValue s i a = Z.componentChartValue s i i := ha.1.2
  have hqj : Z.componentChartValue s j a = Z.componentChartValue s j j := ha.2.2
  rw [← hqi, ← Z.componentChartValue_transition s hs i j a ha.1.1 ha.2.1, hqj,
    inv_mul_cancel]

def reducedTransition (i j a : P) :
    Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) := by
  classical
  exact if ha : a ∈ Z.reducedBaseSet s i ∩ Z.reducedBaseSet s j then
    ⟨(Z.componentRepresentative s j)⁻¹ * Z.transition i j a * Z.componentRepresentative s i,
      Z.reducedTransition_mem s hs i j a ha⟩ else 1

theorem reducedTransition_val (i j a : P)
    (ha : a ∈ Z.reducedBaseSet s i ∩ Z.reducedBaseSet s j) :
    (Z.reducedTransition s hs i j a : bodyAutomorphismGroup S) =
      (Z.componentRepresentative s j)⁻¹ * Z.transition i j a * Z.componentRepresentative s i := by
  simp only [reducedTransition, dif_pos ha]

theorem reducedTransition_self (i a : P) (ha : a ∈ Z.reducedBaseSet s i) :
    Z.reducedTransition s hs i i a = 1 := by
  apply Subtype.ext
  rw [Z.reducedTransition_val s hs i i a ⟨ha, ha⟩, Z.transition_self i a ha.1]
  simp

theorem reducedTransition_cocycle (i j k a : P)
    (hi : a ∈ Z.reducedBaseSet s i) (hj : a ∈ Z.reducedBaseSet s j)
    (hk : a ∈ Z.reducedBaseSet s k) :
    Z.reducedTransition s hs j k a * Z.reducedTransition s hs i j a =
      Z.reducedTransition s hs i k a := by
  apply Subtype.ext
  change (Z.reducedTransition s hs j k a : bodyAutomorphismGroup S) *
      (Z.reducedTransition s hs i j a : bodyAutomorphismGroup S) = _
  rw [Z.reducedTransition_val s hs j k a ⟨hj, hk⟩,
    Z.reducedTransition_val s hs i j a ⟨hi, hj⟩,
    Z.reducedTransition_val s hs i k a ⟨hi, hk⟩]
  simp only [mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc (Z.transition j k a), Z.transition_cocycle i j k a hi.1 hj.1 hk.1]

theorem continuousOn_reducedTransition (i j : P) :
    ContinuousOn (Z.reducedTransition s hs i j)
      (Z.reducedBaseSet s i ∩ Z.reducedBaseSet s j) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  have hT := (Z.continuousOn_transition i j).mono
    (show Z.reducedBaseSet s i ∩ Z.reducedBaseSet s j ⊆ Z.baseSet i ∩ Z.baseSet j from
      fun _ ha => ⟨ha.1.1, ha.2.1⟩)
  have hraw : ContinuousOn (fun a => (Z.componentRepresentative s j)⁻¹ *
      Z.transition i j a * Z.componentRepresentative s i)
      (Z.reducedBaseSet s i ∩ Z.reducedBaseSet s j) :=
    (continuousOn_const.mul hT).mul continuousOn_const
  apply hraw.congr
  intro a ha
  exact Z.reducedTransition_val s hs i j a ha

/-- A genuine bundle core with the connected identity component as its
fiber and actual adjusted principal transition maps. -/
def connectedReductionCore
    (hopen : IsOpen (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) :
      Set (bodyAutomorphismGroup S))) :
    FiberBundleCore P P (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) where
  baseSet := Z.reducedBaseSet s
  isOpen_baseSet := Z.isOpen_reducedBaseSet s hs hopen
  indexAt := id
  mem_baseSet_at := Z.mem_reducedBaseSet s
  coordChange i j a g := Z.reducedTransition s hs i j a * g
  coordChange_self := by
    intro i a ha g
    rw [Z.reducedTransition_self s hs i a ha, one_mul]
  continuousOn_coordChange := by
    intro i j
    have hT : ContinuousOn
        (fun z : P × Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) =>
          Z.reducedTransition s hs i j z.1)
        ((Z.reducedBaseSet s i ∩ Z.reducedBaseSet s j) ×ˢ univ) :=
      (Z.continuousOn_reducedTransition s hs i j).comp
        continuous_fst.continuousOn (fun _ hz => hz.1)
    exact hT.mul continuous_snd.continuousOn
  coordChange_comp := by
    intro i j k a ha g
    rw [← mul_assoc, Z.reducedTransition_cocycle s hs i j k a ha.1.1 ha.1.2 ha.2]

end BanachIsometric.ExactSectionAtlas
