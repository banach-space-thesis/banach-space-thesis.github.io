import BanachIsometric.ConnectedReductionAtlas

/-! The connected-component reduction is mapped into the original principal
bundle by actual continuous operators on its genuine core total space. -/

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

include hs in
theorem componentChartValue_self (a : P) : Z.componentChartValue s a a =
    (show ComponentGroup (S := S) from (s a).2) := by
  have hbase : (s a).1 = a := hs a
  change QuotientGroup.mk (Z.transition (s a).1 a (s a).1) *
    (show ComponentGroup (S := S) from (s a).2) = _
  rw [hbase, Z.transition_self a a (Z.mem_baseSet a), QuotientGroup.mk_one, one_mul]

def connectedReductionToPrincipal (t : (Z.connectedReductionCore s hs hopen).TotalSpace) :
    Z.fiberBundleCore.TotalSpace :=
  ⟨t.1, Z.componentRepresentative s t.1 *
    ((show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from t.2) : bodyAutomorphismGroup S)⟩

@[simp] theorem connectedReductionToPrincipal_proj
    (t : (Z.connectedReductionCore s hs hopen).TotalSpace) :
    Z.fiberBundleCore.proj (Z.connectedReductionToPrincipal s hs hopen t) = t.1 := rfl

theorem connectedReductionToPrincipal_localTriv (i : P)
    (t : (Z.connectedReductionCore s hs hopen).TotalSpace)
    (hi : t.1 ∈ Z.reducedBaseSet s i) :
    Z.fiberBundleCore.localTriv i (Z.connectedReductionToPrincipal s hs hopen t) =
      (t.1, Z.componentRepresentative s i *
        (((Z.connectedReductionCore s hs hopen).localTriv i t).2 : bodyAutomorphismGroup S)) := by
  change (t.1, Z.transition t.1 i t.1 * (Z.componentRepresentative s t.1 *
      ((show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from t.2) : bodyAutomorphismGroup S))) =
    (t.1, Z.componentRepresentative s i *
      ((Z.reducedTransition s hs t.1 i t.1 : bodyAutomorphismGroup S) *
        ((show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from t.2) : bodyAutomorphismGroup S)))
  rw [Z.reducedTransition_val s hs t.1 i t.1 ⟨Z.mem_reducedBaseSet s t.1, hi⟩]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem continuous_connectedReductionToPrincipal :
    Continuous (Z.connectedReductionToPrincipal s hs hopen) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let i := t.1
  have hmem : t.1 ∈ Z.reducedBaseSet s i := Z.mem_reducedBaseSet s t.1
  have hU : (Z.connectedReductionCore s hs hopen).proj ⁻¹' Z.reducedBaseSet s i ∈ 𝓝 t :=
    ((Z.isOpen_reducedBaseSet s hs hopen i).preimage
      (Z.connectedReductionCore s hs hopen).continuous_proj).mem_nhds hmem
  have hV : (Z.connectedReductionToPrincipal s hs hopen) ⁻¹'
      (Z.fiberBundleCore.localTriv i).source ∈ 𝓝 t :=
    mem_of_superset hU (fun _ ha => ha.1)
  apply ((Z.fiberBundleCore.localTriv i).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left hV).mpr
  have hsource := ((Z.connectedReductionCore s hs hopen).localTriv i).continuousAt hmem
  have hmap : Continuous (fun z : P × Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) =>
      (z.1, Z.componentRepresentative s i * (z.2 : bodyAutomorphismGroup S))) :=
    continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
  have hcont := hmap.continuousAt.comp hsource
  apply hcont.congr_of_eventuallyEq
  filter_upwards [hU] with x hx
  exact Z.connectedReductionToPrincipal_localTriv s hs hopen i x hx

theorem connectedReductionToPrincipal_component
    (t : (Z.connectedReductionCore s hs hopen).TotalSpace) :
    Z.componentProjection (Z.connectedReductionToPrincipal s hs hopen t) = s t.1 := by
  apply Bundle.TotalSpace.ext (hs t.1).symm
  apply heq_of_eq
  have hz : (QuotientGroup.mk
      (((show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from t.2)) : bodyAutomorphismGroup S) :
      ComponentGroup (S := S)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr t.2.property
  change (QuotientGroup.mk (Z.componentRepresentative s t.1 *
    ((show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from t.2) : bodyAutomorphismGroup S)) :
      ComponentGroup (S := S)) = (show ComponentGroup (S := S) from (s t.1).2)
  rw [QuotientGroup.mk_mul, hz, mul_one, Z.componentRepresentative_class s t.1,
    Z.componentChartValue_self s hs t.1]

theorem connectedReductionToPrincipal_injective :
    Function.Injective (Z.connectedReductionToPrincipal s hs hopen) := by
  intro t u h
  have hb : t.1 = u.1 := congrArg (fun z : Z.fiberBundleCore.TotalSpace => z.1) h
  cases t with
  | mk a x =>
    cases u with
    | mk b y =>
      change a = b at hb
      subst b
      have hxy : Z.componentRepresentative s a *
          ((show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from x) : bodyAutomorphismGroup S) =
          Z.componentRepresentative s a *
          ((show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from y) : bodyAutomorphismGroup S) :=
        congrArg (fun z : Z.fiberBundleCore.TotalSpace =>
          (show bodyAutomorphismGroup S from z.2)) h
      have he : x = y := Subtype.ext (mul_left_cancel hxy)
      cases he
      rfl

/-- The actual reduced total space maps precisely onto the chosen component
subbundle, rather than onto an unrelated bundle with the same fiber. -/
theorem range_connectedReductionToPrincipal :
    Set.range (Z.connectedReductionToPrincipal s hs hopen) =
      {t : Z.fiberBundleCore.TotalSpace | Z.componentProjection t = s t.1} := by
  ext t
  constructor
  · rintro ⟨u, rfl⟩
    exact Z.connectedReductionToPrincipal_component s hs hopen u
  · intro ht
    let g : bodyAutomorphismGroup S := (Z.componentRepresentative s t.1)⁻¹ *
      (show bodyAutomorphismGroup S from t.2)
    have hclass : (QuotientGroup.mk (show bodyAutomorphismGroup S from t.2) :
        ComponentGroup (S := S)) = (show ComponentGroup (S := S) from (s t.1).2) :=
      congrArg (fun z : Z.componentCore.TotalSpace =>
        (show ComponentGroup (S := S) from z.2)) ht
    have hrep : (QuotientGroup.mk (Z.componentRepresentative s t.1) : ComponentGroup (S := S)) =
        (show ComponentGroup (S := S) from (s t.1).2) :=
      (Z.componentRepresentative_class s t.1).trans (Z.componentChartValue_self s hs t.1)
    have hg : g ∈ Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk ((Z.componentRepresentative s t.1)⁻¹ *
        (show bodyAutomorphismGroup S from t.2)) : ComponentGroup (S := S)) = 1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hclass, hrep, inv_mul_cancel]
    let u : (Z.connectedReductionCore s hs hopen).TotalSpace := ⟨t.1, ⟨g, hg⟩⟩
    refine ⟨u, ?_⟩
    apply Bundle.TotalSpace.ext
    · rfl
    apply heq_of_eq
    change Z.componentRepresentative s t.1 * ((Z.componentRepresentative s t.1)⁻¹ *
      (show bodyAutomorphismGroup S from t.2)) = _
    simp only [mul_inv_cancel_left]

end BanachIsometric.ExactSectionAtlas
