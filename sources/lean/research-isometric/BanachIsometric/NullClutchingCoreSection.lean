import BanachIsometric.ClutchingTrivialization
import BanachIsometric.ConnectedHemisphereClutching

/-! Null clutching constructs an actual continuous section of the original
core, the input required by the already proved Lipschitz regularization. -/

noncomputable section

namespace BanachIsometric

open Set Metric
open scoped Topology

def identityComponentInclusion (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    C(Subgroup.connectedComponentOfOne G, G) := ⟨Subtype.val, continuous_subtype_val⟩

def identityComponentHomotopyToGroup
    {Q G : Type*} [TopologicalSpace Q] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (g : C(Q, Subgroup.connectedComponentOfOne G))
    (h : ContinuousMap.Homotopy (ContinuousMap.const _ (1 : Subgroup.connectedComponentOfOne G)) g) :
    ContinuousMap.Homotopy (ContinuousMap.const _ (1 : G)) ((identityComponentInclusion G).comp g) := by
  let hG := (ContinuousMap.Homotopy.refl (identityComponentInclusion G)).comp h
  apply hG.cast _ rfl
  ext q
  rfl

theorem ExactSectionAtlas.exists_coreSection_of_null_clutching
    {V E F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : sphere (0 : V) 1 → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H) (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (north : C(closedHemisphere v, E →L[ℝ] F))
    (south : C(closedHemisphere (-v), E →L[ℝ] F))
    (hnorth : ∀ x, Function.Injective (north x) ∧ LinearMap.range (north x).toLinearMap = H x.val ∧
      north x '' S = K ∩ (H x.val : Set F))
    (hsouth : ∀ x, Function.Injective (south x) ∧ LinearMap.range (south x).toLinearMap = H x.val ∧
      south x '' S = K ∩ (H x.val : Set F))
    (g : C(EquatorSphere v, bodyAutomorphismGroup S))
    (hglue : ∀ z, south (equatorSouth v z) = (north (equatorNorth v z)).comp
      ((g z).val : E →L[ℝ] E))
    (hnull : ContinuousMap.Homotopy (ContinuousMap.const _ (1 : bodyAutomorphismGroup S)) g) :
    ∃ sec : C(sphere (0 : V) 1, Z.fiberBundleCore.TotalSpace),
      ∀ x, Z.fiberBundleCore.proj (sec x) = x := by
  obtain ⟨out, hout⟩ := exists_global_exact_section_of_null_clutching
    v q₀ north south hnorth hsouth g hglue hnull
  let actual := ExactSectionAtlas.exactOperatorFamily (ContinuousMap.id _) out hout
  let inv : C(ExactSectionSpace S K H, Z.fiberBundleCore.TotalSpace) :=
    ⟨Z.actualHomeomorph.symm, Z.actualHomeomorph.symm.continuous⟩
  let sec := inv.comp actual
  exact ⟨sec, fun _ => rfl⟩

end BanachIsometric
