import BanachIsometric.SuspensionBandRestrictions
import BanachIsometric.ClutchingTrivialization

/-! Null clutching constructs exact operators for the SAME supplied actual
suspension map whose degree may have been computed separately. Its full band
action is explicit, so distinct existential sphere-map witnesses are never
identified implicitly. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology

theorem exists_exact_section_for_supplied_suspension_of_null_clutching
    {V E F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : sphere (0 : V) 1 → Submodule ℝ F}
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (north : C(closedHemisphere v, E →L[ℝ] F))
    (south : C(closedHemisphere (-v), E →L[ℝ] F))
    (hnorth : ∀ x, Function.Injective (north x) ∧ LinearMap.range (north x).toLinearMap = H x.val ∧
      north x '' S = K ∩ (H x.val : Set F))
    (hsouth : ∀ x, Function.Injective (south x) ∧ LinearMap.range (south x).toLinearMap = H x.val ∧
      south x '' S = K ∩ (H x.val : Set F))
    (g : C(EquatorSphere v, bodyAutomorphismGroup S))
    (hglue : ∀ z, south (equatorSouth v z) = (north (equatorNorth v z)).comp
      ((g z).val : E →L[ℝ] E))
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hband : ∀ a : Icc (-1 : ℝ) 1, ∀ z, φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    (hnull : ContinuousMap.Homotopy
      (ContinuousMap.const _ (1 : bodyAutomorphismGroup S)) (g.comp f)) :
    ∃ out : C(sphere (0 : V) 1, E →L[ℝ] F),
      ∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H (φ x) ∧
        out x '' S = K ∩ (H (φ x) : Set F) := by
  obtain ⟨hφN, hφS⟩ := suspension_restrictions_of_band_action v q₀ f φ hband
  let N := hemisphereMap v q₀ f
  let T := hemisphereMap (-v) (equatorOppositePole v q₀) (oppositeEquatorMap v f)
  let north' := north.comp N
  let south' := south.comp T
  have hnorth' : ∀ x, Function.Injective (north' x) ∧
      LinearMap.range (north' x).toLinearMap = H (φ x.val) ∧
      north' x '' S = K ∩ (H (φ x.val) : Set F) := by
    intro x
    rw [hφN x]
    exact hnorth (N x)
  have hsouth' : ∀ x, Function.Injective (south' x) ∧
      LinearMap.range (south' x).toLinearMap = H (φ x.val) ∧
      south' x '' S = K ∩ (H (φ x.val) : Set F) := by
    intro x
    rw [hφS x]
    exact hsouth (T x)
  have hglue' : ∀ z, south' (equatorSouth v z) = (north' (equatorNorth v z)).comp
      (((g.comp f) z).val : E →L[ℝ] E) := by
    intro z
    change south (T (equatorSouth v z)) = (north (N (equatorNorth v z))).comp
      ((g (f z)).val : E →L[ℝ] E)
    dsimp only [T, N]
    rw [hemisphereMap_south_equator, hemisphereMap_equator]
    exact hglue (f z)
  exact exists_global_exact_section_of_null_clutching
    (H := fun x => H (φ x)) v q₀ north' south' hnorth' hsouth' (g.comp f) hglue' hnull

end BanachIsometric
