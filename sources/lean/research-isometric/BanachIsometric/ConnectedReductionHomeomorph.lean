import BanachIsometric.ConnectedReductionMap

/-! The actual connected reduction is homeomorphic to the selected component
subbundle in the original total space's inherited topology. -/

noncomputable section

namespace BanachIsometric.ExactSectionAtlas

open Set Bundle Filter
open scoped Topology
attribute [local instance] BanachIsometric.connectedComponentOfOne_normal

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : BanachIsometric.ExactSectionAtlas S K H)
    (s : C(P, Z.componentCore.TotalSpace)) (hs : ∀ a, Z.componentCore.proj (s a) = a)
    (hopen : IsOpen (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) :
      Set (bodyAutomorphismGroup S)))

def SelectedComponent := {t : Z.fiberBundleCore.TotalSpace | Z.componentProjection t = s t.1}

def connectedReductionEquiv : (Z.connectedReductionCore s hs hopen).TotalSpace ≃
    Z.SelectedComponent s :=
  Equiv.ofBijective
    (fun u => ⟨Z.connectedReductionToPrincipal s hs hopen u,
      Z.connectedReductionToPrincipal_component s hs hopen u⟩)
    ⟨fun _ _ h => Z.connectedReductionToPrincipal_injective s hs hopen (congrArg Subtype.val h), by
      intro t
      have ht : t.val ∈ Set.range (Z.connectedReductionToPrincipal s hs hopen) := by
        rw [Z.range_connectedReductionToPrincipal s hs hopen]
        exact t.property
      obtain ⟨u, hu⟩ := ht
      exact ⟨u, Subtype.ext hu⟩⟩

theorem connectedReductionEquiv_symm_proj (t : Z.SelectedComponent s) :
    ((Z.connectedReductionEquiv s hs hopen).symm t).1 = t.val.1 :=
  congrArg (fun z : Z.SelectedComponent s => z.val.1)
    ((Z.connectedReductionEquiv s hs hopen).apply_symm_apply t)

theorem connectedReductionEquiv_symm_localTriv (i : P) (t : Z.SelectedComponent s)
    (hi : t.val.1 ∈ Z.reducedBaseSet s i) :
    (((Z.connectedReductionCore s hs hopen).localTriv i
        ((Z.connectedReductionEquiv s hs hopen).symm t)).1,
      (((Z.connectedReductionCore s hs hopen).localTriv i
        ((Z.connectedReductionEquiv s hs hopen).symm t)).2 : bodyAutomorphismGroup S)) =
    ((Z.fiberBundleCore.localTriv i t.val).1,
      (Z.componentRepresentative s i)⁻¹ * (Z.fiberBundleCore.localTriv i t.val).2) := by
  let u := (Z.connectedReductionEquiv s hs hopen).symm t
  have hbase : u.1 = t.val.1 := Z.connectedReductionEquiv_symm_proj s hs hopen t
  have him : Z.connectedReductionToPrincipal s hs hopen u = t.val :=
    congrArg Subtype.val ((Z.connectedReductionEquiv s hs hopen).apply_symm_apply t)
  have hloc := Z.connectedReductionToPrincipal_localTriv s hs hopen i u (hbase ▸ hi)
  rw [him] at hloc
  apply Prod.ext
  · exact hbase
  · rw [congrArg Prod.snd hloc]
    simp only [inv_mul_cancel_left]
    rfl

theorem continuous_connectedReductionEquiv_symm :
    Continuous (Z.connectedReductionEquiv s hs hopen).symm := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let i := ((Z.connectedReductionEquiv s hs hopen).symm t).1
  have hi : t.val.1 ∈ Z.reducedBaseSet s i := by
    rw [← Z.connectedReductionEquiv_symm_proj s hs hopen t]
    exact Z.mem_reducedBaseSet s i
  have hbase : Continuous (fun z : Z.SelectedComponent s => z.val.1) :=
    Z.fiberBundleCore.continuous_proj.comp continuous_subtype_val
  have hU : (fun z : Z.SelectedComponent s => z.val.1) ⁻¹' Z.reducedBaseSet s i ∈ 𝓝 t :=
    ((Z.isOpen_reducedBaseSet s hs hopen i).preimage hbase).mem_nhds hi
  have hV : (Z.connectedReductionEquiv s hs hopen).symm ⁻¹'
      ((Z.connectedReductionCore s hs hopen).localTriv i).source ∈ 𝓝 t := by
    filter_upwards [hU] with z hz
    change ((Z.connectedReductionEquiv s hs hopen).symm z).1 ∈ Z.reducedBaseSet s i
    rw [Z.connectedReductionEquiv_symm_proj s hs hopen z]
    exact hz
  apply (((Z.connectedReductionCore s hs hopen).localTriv i).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    hV).mpr
  have hind : Topology.IsInducing
      (fun z : P × Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) =>
        (z.1, (z.2 : bodyAutomorphismGroup S))) :=
    Topology.IsInducing.id.prodMap Topology.IsInducing.subtypeVal
  apply hind.continuousAt_iff.mpr
  have htriv : ContinuousAt (fun z : Z.SelectedComponent s => Z.fiberBundleCore.localTriv i z.val) t :=
    ((Z.fiberBundleCore.localTriv i).continuousAt hi.1).comp continuous_subtype_val.continuousAt
  have hmap : Continuous (fun z : P × bodyAutomorphismGroup S =>
      (z.1, (Z.componentRepresentative s i)⁻¹ * z.2)) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  apply (hmap.continuousAt.comp htriv).congr_of_eventuallyEq
  filter_upwards [hU] with z hz
  exact Z.connectedReductionEquiv_symm_localTriv s hs hopen i z hz

def connectedReductionHomeomorph : (Z.connectedReductionCore s hs hopen).TotalSpace ≃ₜ
    Z.SelectedComponent s where
  toEquiv := Z.connectedReductionEquiv s hs hopen
  continuous_toFun := (Z.continuous_connectedReductionToPrincipal s hs hopen).subtype_mk _
  continuous_invFun := Z.continuous_connectedReductionEquiv_symm s hs hopen

end BanachIsometric.ExactSectionAtlas
