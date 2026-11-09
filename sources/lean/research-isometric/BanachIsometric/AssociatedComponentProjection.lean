import BanachIsometric.ComponentBundleReduction

/-! The associated component covering is linked to the original principal
core by the actual continuous fiberwise quotient map, with exact chart
compatibility. Thus the covering is the concrete associated construction. -/

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

def componentProjection (t : Z.fiberBundleCore.TotalSpace) : Z.componentCore.TotalSpace :=
  ⟨t.1, (QuotientGroup.mk (show bodyAutomorphismGroup S from t.2) : ComponentGroup (S := S))⟩

@[simp] theorem componentProjection_proj (t : Z.fiberBundleCore.TotalSpace) :
    Z.componentCore.proj (Z.componentProjection t) = Z.fiberBundleCore.proj t := rfl

theorem componentProjection_localTriv (i : P) (t : Z.fiberBundleCore.TotalSpace) :
    Z.componentCore.localTriv i (Z.componentProjection t) =
      ((Z.fiberBundleCore.localTriv i t).1,
        (QuotientGroup.mk (Z.fiberBundleCore.localTriv i t).2 : ComponentGroup (S := S))) := by
  change (t.1, QuotientGroup.mk (Z.transition t.1 i t.1) *
      (QuotientGroup.mk (show bodyAutomorphismGroup S from t.2) : ComponentGroup (S := S))) =
    (t.1, (QuotientGroup.mk (Z.transition t.1 i t.1 *
      (show bodyAutomorphismGroup S from t.2)) : ComponentGroup (S := S)))
  rw [QuotientGroup.mk_mul]

theorem continuous_componentProjection : Continuous Z.componentProjection := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let i := t.1
  have hmem : t.1 ∈ Z.baseSet i := Z.mem_baseSet t.1
  have hnhds : Z.componentProjection ⁻¹' (Z.componentCore.localTriv i).source ∈ 𝓝 t := by
    change Z.fiberBundleCore.proj ⁻¹' Z.baseSet i ∈ 𝓝 t
    exact (Z.fiberBundleCore.isOpen_baseSet i).preimage
      Z.fiberBundleCore.continuous_proj |>.mem_nhds hmem
  apply ((Z.componentCore.localTriv i).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    hnhds).mpr
  have hsource : ContinuousAt (Z.fiberBundleCore.localTriv i) t :=
    (Z.fiberBundleCore.localTriv i).continuousAt hmem
  have hmap : Continuous (fun z : P × bodyAutomorphismGroup S =>
      (z.1, (QuotientGroup.mk z.2 : ComponentGroup (S := S)))) :=
    continuous_fst.prodMk (QuotientGroup.continuous_mk.comp continuous_snd)
  have hEq : (fun x : Z.fiberBundleCore.TotalSpace =>
      Z.componentCore.localTriv i (Z.componentProjection x)) =
      (fun x => ((Z.fiberBundleCore.localTriv i x).1,
        (QuotientGroup.mk (Z.fiberBundleCore.localTriv i x).2 : ComponentGroup (S := S)))) :=
    funext (Z.componentProjection_localTriv i)
  change ContinuousAt (fun x => Z.componentCore.localTriv i (Z.componentProjection x)) t
  rw [hEq]
  exact hmap.continuousAt.comp hsource

theorem componentProjection_surjective : Function.Surjective Z.componentProjection := by
  rintro ⟨a, q⟩
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (show ComponentGroup (S := S) from q)
  exact ⟨⟨a, g⟩, by cases hg; rfl⟩

end BanachIsometric.ExactSectionAtlas
