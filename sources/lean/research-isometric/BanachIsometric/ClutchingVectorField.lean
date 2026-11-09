import BanachIsometric.ClutchingTrivialization
import BanachIsometric.SphereAvoidedPointHomotopy

/-! A null-homotopy of one evaluated clutching vector, rather than of the
whole clutching map, suffices to construct a nowhere-zero tangent field.
The local frames need only be injective and tangent; they need not be isometric. -/

noncomputable section

namespace BanachIsometric

open Set Metric NormedSpace
open scoped Topology

theorem exists_nonzero_tangent_field_of_avoided_clutching_vector
    {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E}
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (north : C(closedHemisphere v, E →L[ℝ] V))
    (south : C(closedHemisphere (-v), E →L[ℝ] V))
    (hnorth : ∀ x, Function.Injective (north x) ∧
      ∀ y, inner ℝ x.val.val (north x y) = 0)
    (hsouth : ∀ x, Function.Injective (south x) ∧
      ∀ y, inner ℝ x.val.val (south x y) = 0)
    (g : C(EquatorSphere v, bodyAutomorphismGroup S))
    (hglue : ∀ z, south (equatorSouth v z) = (north (equatorNorth v z)).comp
      ((g z).val : E →L[ℝ] E))
    (w : sphere (0 : E) 1)
    (hunit : ∀ z, ‖((g z).val : E →L[ℝ] E) w.val‖ = 1)
    (p : sphere (0 : E) 1)
    (havoid : ∀ z, ((g z).val : E →L[ℝ] E) w.val ≠ p.val) :
    ∃ out : C(sphere (0 : V) 1, V), ∀ x,
      out x ≠ 0 ∧ inner ℝ x.val (out x) = 0 := by
  have hgc : Continuous (fun z => ((g z).val : E →L[ℝ] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp g.continuous)
  let f : C(EquatorSphere v, sphere (0 : E) 1) := by
    refine ⟨fun z => ⟨((g z).val : E →L[ℝ] E) w.val, ?_⟩, ?_⟩
    · simpa only [mem_sphere, dist_zero_right] using hunit z
    · exact (hgc.clm_apply continuous_const).subtype_mk _
  have hf : ∀ z, f z ≠ p := by
    intro z hz
    exact havoid z (congrArg Subtype.val hz)
  obtain ⟨e, he⟩ := exists_hemisphere_extension_of_homotopy_from_constant v q₀ f (-p)
    (sphereAvoidedPointHomotopy f p hf)
  let north' : C(closedHemisphere v, V) :=
    ⟨fun x => north x (e x).val,
      north.continuous.clm_apply (continuous_subtype_val.comp e.continuous)⟩
  let south' : C(closedHemisphere (-v), V) :=
    ⟨fun x => south x w.val, south.continuous.clm_apply continuous_const⟩
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
      north' ⟨x, hx⟩ = south' ⟨x, hy⟩ := by
    intro x hx hy
    have hz : inner ℝ v.val x.val = 0 := by
      change 0 ≤ inner ℝ v.val x.val at hx
      change 0 ≤ inner ℝ (-v.val) x.val at hy
      rw [inner_neg_left] at hy
      linarith
    let z : EquatorSphere v := ⟨⟨x.val,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hz⟩, by
      rw [mem_sphere, dist_zero_right]
      exact norm_eq_of_mem_sphere x⟩
    have hn : equatorNorth v z = ⟨x, hx⟩ := by apply Subtype.ext; apply Subtype.ext; rfl
    have hs : equatorSouth v z = ⟨x, hy⟩ := by apply Subtype.ext; apply Subtype.ext; rfl
    have hboundary : north' (equatorNorth v z) = south' (equatorSouth v z) := by
      change north (equatorNorth v z) (e (equatorNorth v z)).val =
        south (equatorSouth v z) w.val
      rw [he z, hglue z]
      rfl
    simpa only [hn, hs] using hboundary
  obtain ⟨out, hN, hS⟩ := exists_continuousMap_glue_closed_cover
    hNclosed hSclosed hcover north' south' hagree
  refine ⟨out, ?_⟩
  intro x
  have hx : x ∈ closedHemisphere v ∪ closedHemisphere (-v) := hcover ▸ mem_univ x
  rcases hx with hx | hx
  · rw [hN ⟨x, hx⟩]
    refine ⟨?_, (hnorth ⟨x, hx⟩).2 _⟩
    intro hz
    have he0 : (e ⟨x, hx⟩).val = 0 :=
      (hnorth ⟨x, hx⟩).1 (hz.trans (map_zero _).symm)
    have hnorm := norm_eq_of_mem_sphere (e ⟨x, hx⟩)
    rw [he0, norm_zero] at hnorm
    norm_num at hnorm
  · rw [hS ⟨x, hx⟩]
    refine ⟨?_, (hsouth ⟨x, hx⟩).2 _⟩
    intro hz
    have hw0 : w.val = 0 :=
      (hsouth ⟨x, hx⟩).1 (hz.trans (map_zero _).symm)
    have hnorm := norm_eq_of_mem_sphere w
    rw [hw0, norm_zero] at hnorm
    norm_num at hnorm

end BanachIsometric
