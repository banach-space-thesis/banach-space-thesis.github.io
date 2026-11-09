import BanachIsometric.ExactSectionHemisphere
import BanachIsometric.ContinuousExactCoordinates
import BanachIsometric.EquatorCoordinates
import BanachIsometric.BasedConnectedGroupMap

/-! Actual hemisphere frames and their genuine continuous equatorial
clutching map, all constructed from the original exact-section geometry. -/

noncomputable section

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology NNReal

theorem ExactSectionPrincipalData.exists_hemisphere_clutching
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : V) 1 → Submodule ℝ F}
    {a₀ : sphere (0 : V) 1} (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (v : sphere (0 : V) 1) :
    ∃ north : C(closedHemisphere v, EuclideanSpace ℝ (Fin m) →L[ℝ] F),
    ∃ south : C(closedHemisphere (-v), EuclideanSpace ℝ (Fin m) →L[ℝ] F),
    ∃ g : C(EquatorSphere v, D.StructureGroup),
      (∀ x, Function.Injective (north x) ∧ LinearMap.range (north x).toLinearMap = H x.val ∧
        north x '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H x.val : Set F)) ∧
      (∀ x, Function.Injective (south x) ∧ LinearMap.range (south x).toLinearMap = H x.val ∧
        south x '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H x.val : Set F)) ∧
      ∀ x, south (equatorSouth v x) = (north (equatorNorth v x)).comp
        ((g x).val : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) := by
  obtain ⟨north, hnorth, _⟩ := D.exists_continuous_hemisphere_section μ hp hC hProj v
    (D.atlas.exactMap v v (D.atlas.mem_baseSet v))
  obtain ⟨south, hsouth, _⟩ := D.exists_continuous_hemisphere_section μ hp hC hProj (-v)
    (D.atlas.exactMap (-v) (-v) (D.atlas.mem_baseSet (-v)))
  let A := north.comp (equatorNorth v)
  let B := south.comp (equatorSouth v)
  have hA : ∀ x, Function.Injective (A x) ∧ LinearMap.range (A x).toLinearMap = H (equatorInclusion v x) ∧
      A x '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (equatorInclusion v x) : Set F) := by
    intro x
    exact hnorth (equatorNorth v x)
  have hB : ∀ x, Function.Injective (B x) ∧ LinearMap.range (B x).toLinearMap = H (equatorInclusion v x) ∧
      B x '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (equatorInclusion v x) : Set F) := by
    intro x
    exact hsouth (equatorSouth v x)
  let g : C(EquatorSphere v, D.StructureGroup) :=
    ⟨ExactSectionAtlas.exactCoordinateFamily (equatorInclusion v) A B hA hB,
      D.atlas.continuous_exactCoordinateFamily (equatorInclusion v) A B hA hB⟩
  refine ⟨north, south, g, hnorth, hsouth, ?_⟩
  intro x
  exact (congrArg Subtype.val (exactBodyMapRight_coordinate
    (⟨A x, hA x⟩ : ExactBodyMap D.ModelBody {y : F | p y ≤ 1} (H (equatorInclusion v x)))
    ⟨B x, hB x⟩)).symm

end BanachIsometric
