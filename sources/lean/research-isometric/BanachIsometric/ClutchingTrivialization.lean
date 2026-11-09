import BanachIsometric.HemisphereNullhomotopyExtension
import BanachIsometric.ClosedCoverGluing
import BanachIsometric.ContinuousExactCoordinates

/-! Null-homotopic actual hemisphere clutching gives an actual global exact
operator section, by extending over the cone and gluing the closed hemispheres.
This proves the needed direction constructively, without a bundle classifier. -/

noncomputable section

namespace BanachIsometric

open Set Metric
open scoped Topology

theorem exists_global_exact_section_of_null_clutching
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
    (hnull : ContinuousMap.Homotopy (ContinuousMap.const _ (1 : bodyAutomorphismGroup S)) g) :
    ∃ out : C(sphere (0 : V) 1, E →L[ℝ] F),
      ∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H x ∧
        out x '' S = K ∩ (H x : Set F) := by
  obtain ⟨e, he⟩ := exists_hemisphere_extension_of_homotopy_from_constant v q₀ g 1 hnull
  have hEc : Continuous (fun x => ((e x).val : E →L[ℝ] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp e.continuous)
  let north' : C(closedHemisphere v, E →L[ℝ] F) :=
    ⟨fun x => (north x).comp ((e x).val : E →L[ℝ] E), north.continuous.clm_comp hEc⟩
  have hnorth' : ∀ x, Function.Injective (north' x) ∧ LinearMap.range (north' x).toLinearMap = H x.val ∧
      north' x '' S = K ∩ (H x.val : Set F) := fun x =>
    (exactBodyMapRight (⟨north x, hnorth x⟩ : ExactBodyMap S K (H x.val)) (e x)).property
  have hNclosed : IsClosed (closedHemisphere v) :=
    isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
  have hSclosed : IsClosed (closedHemisphere (-v)) :=
    isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
  have hcover : closedHemisphere v ∪ closedHemisphere (-v) = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : 0 ≤ inner ℝ v.val x.val
    · exact Or.inl hx
    · right
      change 0 ≤ inner ℝ (-v.val) x.val
      rw [inner_neg_left]
      linarith
  have hagree : ∀ x (hx : x ∈ closedHemisphere v) (hy : x ∈ closedHemisphere (-v)),
      north' ⟨x, hx⟩ = south ⟨x, hy⟩ := by
    intro x hx hy
    have hz : inner ℝ v.val x.val = 0 := by
      change 0 ≤ inner ℝ v.val x.val at hx
      change 0 ≤ inner ℝ (-v.val) x.val at hy
      rw [inner_neg_left] at hy
      linarith
    let z : EquatorSphere v := ⟨⟨x.val, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hz⟩, by
      rw [Metric.mem_sphere, dist_zero_right]
      exact norm_eq_of_mem_sphere x⟩
    have hn : equatorNorth v z = ⟨x, hx⟩ := by apply Subtype.ext; apply Subtype.ext; rfl
    have hs : equatorSouth v z = ⟨x, hy⟩ := by apply Subtype.ext; apply Subtype.ext; rfl
    have hboundary : north' (equatorNorth v z) = south (equatorSouth v z) := by
      change (north (equatorNorth v z)).comp ((e (equatorNorth v z)).val : E →L[ℝ] E) = _
      rw [he z]
      exact (hglue z).symm
    simpa only [hn, hs] using hboundary
  obtain ⟨out, hN, hS⟩ := exists_continuousMap_glue_closed_cover hNclosed hSclosed hcover north' south hagree
  refine ⟨out, ?_⟩
  intro x
  have hx : x ∈ closedHemisphere v ∪ closedHemisphere (-v) := hcover ▸ mem_univ x
  rcases hx with hx | hx
  · rw [hN ⟨x, hx⟩]
    exact hnorth' ⟨x, hx⟩
  · rw [hS ⟨x, hx⟩]
    exact hsouth ⟨x, hx⟩

end BanachIsometric
