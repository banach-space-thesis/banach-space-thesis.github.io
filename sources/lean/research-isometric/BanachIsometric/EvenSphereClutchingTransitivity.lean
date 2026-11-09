import BanachIsometric.ClutchingVectorField
import BanachIsometric.SphereTangentObstruction
import BanachIsometric.BodyGroupConjugation

/-! In odd ambient real dimension, an actual tangent-frame clutching map
with isometric model action evaluates surjectively on the model sphere.
Covariance normalization of the fixed body supplies this isometric action.
No homotopy-group torsion or characteristic-class theorem is assumed. -/

noncomputable section

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology

theorem clutching_vector_surjective_of_odd_finrank
    {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} {N : ℕ} [NeZero N]
    (e : V ≃L[ℝ] PiolaSpace N) (hOdd : Odd (Module.finrank ℝ V))
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
    (p : sphere (0 : E) 1) :
    ∃ z, ((g z).val : E →L[ℝ] E) w.val = p.val := by
  by_contra h
  push_neg at h
  obtain ⟨out, hout⟩ := exists_nonzero_tangent_field_of_avoided_clutching_vector
    v q₀ north south hnorth hsouth g hglue w hunit p h
  exact no_nonzero_tangent_sphere_field_of_odd_finrank e hOdd out
    (fun u => (hout u).1) (fun u => (hout u).2)

theorem covariance_bodyGroup_transitive_of_tangent_clutching
    {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {S : Set E} {N : ℕ} [NeZero N]
    (eV : V ≃L[ℝ] PiolaSpace N) (hOdd : Odd (Module.finrank ℝ V))
    (μ : Measure E) [μ.IsAddHaarMeasure] (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ E)
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (north : C(closedHemisphere v, E →L[ℝ] V))
    (south : C(closedHemisphere (-v), E →L[ℝ] V))
    (hnorth : ∀ x, Function.Injective (north x) ∧
      ∀ y, inner ℝ x.val.val (north x y) = 0)
    (hsouth : ∀ x, Function.Injective (south x) ∧
      ∀ y, inner ℝ x.val.val (south x y) = 0)
    (g : C(EquatorSphere v, bodyAutomorphismGroup S))
    (hglue : ∀ z, south (equatorSouth v z) = (north (equatorNorth v z)).comp
      ((g z).val : E →L[ℝ] E)) :
    ∀ w p : sphere (0 : E) 1, ∃ a : bodyAutomorphismGroup S,
      (a.val : E →L[ℝ] E) w.val = p.val := by
  intro w p
  have hunit (z) : ‖((g z).val : E →L[ℝ] E) w.val‖ = 1 := by
    let L := covariancePositionIsometry μ hS hC
      (ContinuousLinearEquiv.ofUnit (g z).val) (g z).property
    exact (L.norm_map w.val).trans (norm_eq_of_mem_sphere w)
  obtain ⟨z, hz⟩ := clutching_vector_surjective_of_odd_finrank
    eV hOdd v q₀ north south hnorth hsouth g hglue w hunit p
  exact ⟨g z, hz⟩

theorem exists_covariance_transitive_bodyGroup_of_tangent_clutching
    {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {S : Set E} {N : ℕ} [NeZero N]
    (eV : V ≃L[ℝ] PiolaSpace N) (hOdd : Odd (Module.finrank ℝ V))
    (μ : Measure E) [μ.IsAddHaarMeasure] (hS : IsCompact S) (h0 : (0 : E) ∈ interior S)
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (north : C(closedHemisphere v, E →L[ℝ] V))
    (south : C(closedHemisphere (-v), E →L[ℝ] V))
    (hnorth : ∀ x, Function.Injective (north x) ∧
      ∀ y, inner ℝ x.val.val (north x y) = 0)
    (hsouth : ∀ x, Function.Injective (south x) ∧
      ∀ y, inner ℝ x.val.val (south x y) = 0)
    (g : C(EquatorSphere v, bodyAutomorphismGroup S))
    (hglue : ∀ z, south (equatorSouth v z) = (north (equatorNorth v z)).comp
      ((g z).val : E →L[ℝ] E)) :
    ∃ e : E ≃L[ℝ] E, covarianceOperator μ (e '' S) = ContinuousLinearMap.id ℝ E ∧
      ∀ w p : sphere (0 : E) 1, ∃ a : bodyAutomorphismGroup (e '' S),
        (a.val : E →L[ℝ] E) w.val = p.val := by
  obtain ⟨e, he⟩ := exists_covariancePosition μ hS h0
  let T := e '' S
  let g' : C(EquatorSphere v, bodyAutomorphismGroup T) :=
    ⟨fun z => bodyAutomorphismConjugationHomeomorph e S T rfl (g z),
      (bodyAutomorphismConjugationHomeomorph e S T rfl).continuous.comp g.continuous⟩
  let north' : C(closedHemisphere v, E →L[ℝ] V) :=
    ⟨fun x => (north x).comp e.symm.toContinuousLinearMap,
      north.continuous.clm_comp continuous_const⟩
  let south' : C(closedHemisphere (-v), E →L[ℝ] V) :=
    ⟨fun x => (south x).comp e.symm.toContinuousLinearMap,
      south.continuous.clm_comp continuous_const⟩
  have hnorth' : ∀ x, Function.Injective (north' x) ∧
      ∀ y, inner ℝ x.val.val (north' x y) = 0 := by
    intro x
    exact ⟨(hnorth x).1.comp e.symm.injective, fun y => (hnorth x).2 (e.symm y)⟩
  have hsouth' : ∀ x, Function.Injective (south' x) ∧
      ∀ y, inner ℝ x.val.val (south' x y) = 0 := by
    intro x
    exact ⟨(hsouth x).1.comp e.symm.injective, fun y => (hsouth x).2 (e.symm y)⟩
  have hglue' : ∀ z, south' (equatorSouth v z) = (north' (equatorNorth v z)).comp
      ((g' z).val : E →L[ℝ] E) := by
    intro z
    apply ContinuousLinearMap.ext
    intro y
    change south (equatorSouth v z) (e.symm y) =
      north (equatorNorth v z) (e.symm (e (((g z).val : E →L[ℝ] E) (e.symm y))))
    rw [e.symm_apply_apply]
    exact congrArg (fun A : E →L[ℝ] V => A (e.symm y)) (hglue z)
  exact ⟨e, he, covariance_bodyGroup_transitive_of_tangent_clutching eV hOdd μ
    (hS.image e.continuous) he v q₀ north' south' hnorth' hsouth' g' hglue'⟩

end BanachIsometric
