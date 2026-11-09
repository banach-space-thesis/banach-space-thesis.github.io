import BanachIsometric.SuppliedSuspensionClutching

/-! Actual nullhomotopy transfer under an actual homotopy of equator maps.
This is postcomposition and concatenation of literal homotopies, rather than
an assumed homotopy invariance of bundle classification. The resulting exact
operators belong to the same supplied suspension map. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology

def nullClutchingHomotopyTransfer
    {Q G : Type*} [TopologicalSpace Q] [TopologicalSpace G] [One G]
    (g : C(Q, G)) {f₀ f₁ : C(Q, Q)}
    (hnull : ContinuousMap.Homotopy (ContinuousMap.const Q (1 : G)) (g.comp f₀))
    (h : ContinuousMap.Homotopy f₀ f₁) :
    ContinuousMap.Homotopy (ContinuousMap.const Q (1 : G)) (g.comp f₁) :=
  hnull.trans ((ContinuousMap.Homotopy.refl g).comp h)

def conjugateSphereHomotopy
    {Q R : Type*} [TopologicalSpace Q] [TopologicalSpace R]
    (e : Q ≃ₜ R) {f₀ f₁ : C(R, R)} (h : ContinuousMap.Homotopy f₀ f₁) :
    ContinuousMap.Homotopy
      ((⟨e.symm, e.symm.continuous⟩ : C(R, Q)).comp (f₀.comp ⟨e, e.continuous⟩))
      ((⟨e.symm, e.symm.continuous⟩ : C(R, Q)).comp (f₁.comp ⟨e, e.continuous⟩)) :=
  (ContinuousMap.Homotopy.refl ⟨e.symm, e.symm.continuous⟩).comp
    (h.compContinuousMap ⟨e, e.continuous⟩)

theorem exists_exact_section_for_supplied_homotopic_suspension_of_null_clutching
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
    {f₀ f₁ : C(EquatorSphere v, EquatorSphere v)}
    (hnull : ContinuousMap.Homotopy
      (ContinuousMap.const _ (1 : bodyAutomorphismGroup S)) (g.comp f₀))
    (h : ContinuousMap.Homotopy f₀ f₁)
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hband : ∀ a : Icc (-1 : ℝ) 1, ∀ z, φ (equatorBand v (a, z)) = equatorBand v (a, f₁ z)) :
    ∃ out : C(sphere (0 : V) 1, E →L[ℝ] F),
      ∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H (φ x) ∧
        out x '' S = K ∩ (H (φ x) : Set F) :=
  exists_exact_section_for_supplied_suspension_of_null_clutching
    v q₀ north south hnorth hsouth g hglue f₁ φ hband (nullClutchingHomotopyTransfer g hnull h)

end BanachIsometric
