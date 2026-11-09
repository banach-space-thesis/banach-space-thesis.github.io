import BanachIsometric.HemisphereClutching

/-! The actual equatorial clutching map takes values in the connected
identity group after an actual constant change of the northern frame.
This direct connected-equator normalization is an alternative way to obtain
the based connected-group clutching map after hemisphere sections exist. -/

noncomputable section

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology NNReal

theorem ExactSectionPrincipalData.exists_connected_hemisphere_clutching
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : V) 1 → Submodule ℝ F}
    {a₀ : sphere (0 : V) 1} (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (v : sphere (0 : V) 1) (hrank : 1 < Module.rank ℝ (ℝ ∙ v.val)ᗮ)
    (q₀ : EquatorSphere v) :
    ∃ north : C(closedHemisphere v, EuclideanSpace ℝ (Fin m) →L[ℝ] F),
    ∃ south : C(closedHemisphere (-v), EuclideanSpace ℝ (Fin m) →L[ℝ] F),
    ∃ g : C(EquatorSphere v, Subgroup.connectedComponentOfOne D.StructureGroup),
      (∀ x, Function.Injective (north x) ∧ LinearMap.range (north x).toLinearMap = H x.val ∧
        north x '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H x.val : Set F)) ∧
      (∀ x, Function.Injective (south x) ∧ LinearMap.range (south x).toLinearMap = H x.val ∧
        south x '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H x.val : Set F)) ∧
      g q₀ = 1 ∧ ∀ x, south (equatorSouth v x) = (north (equatorNorth v x)).comp
        (((g x).val).val : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) := by
  letI := pathConnectedSpace_equator v hrank
  obtain ⟨north, south, raw, hnorth, hsouth, hraw⟩ := D.exists_hemisphere_clutching μ hp hC hProj v
  let g₀ := raw q₀
  let north' : C(closedHemisphere v, EuclideanSpace ℝ (Fin m) →L[ℝ] F) :=
    ⟨fun x => (north x).comp (g₀.val : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)),
      north.continuous.clm_comp continuous_const⟩
  let g := basedIdentityComponentMap raw q₀
  refine ⟨north', south, g, ?_, hsouth, basedIdentityComponentMap_base raw q₀, ?_⟩
  · intro x
    exact (exactBodyMapRight
      (⟨north x, hnorth x⟩ : ExactBodyMap D.ModelBody {y : F | p y ≤ 1} (H x.val)) g₀).property
  · intro x
    rw [hraw x]
    apply ContinuousLinearMap.ext
    intro y
    change north (equatorNorth v x) (((raw x).val : EuclideanSpace ℝ (Fin m) →L[ℝ] _) y) =
      north (equatorNorth v x)
        (((g₀ * (g₀⁻¹ * raw x)).val : EuclideanSpace ℝ (Fin m) →L[ℝ] _) y)
    rw [mul_inv_cancel_left]

end BanachIsometric
