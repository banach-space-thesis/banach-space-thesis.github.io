import BanachIsometric.ExactSectionEndpointTransport
import BanachIsometric.HemisphereContraction

/-! Actual continuous exact-section families on closed hemispheres, with a
specified exact operator at the pole. This is the concrete hemisphere-section
ingredient for clutching, obtained by finite-step contraction transport. -/

noncomputable section

namespace BanachIsometric

open Set Metric NormedSpace MeasureTheory
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def hemispherePole (v : sphere (0 : V) 1) : closedHemisphere v :=
  ⟨v, by
    change 0 ≤ inner ℝ v.val v.val
    exact real_inner_self_nonneg⟩

@[simp] theorem hemisphereContraction_pole (v : sphere (0 : V) 1) (t : unitInterval) :
    hemisphereContraction v (t, hemispherePole v) = v := by
  apply Subtype.ext
  change normalize ((1 - (t : ℝ)) • v.val + (t : ℝ) • v.val) = v.val
  rw [← add_smul, sub_add_cancel, one_smul]
  exact normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere v)

theorem ExactSectionPrincipalData.exists_continuous_hemisphere_section
    [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : V) 1 → Submodule ℝ F}
    {a₀ : sphere (0 : V) 1} (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (v : sphere (0 : V) 1)
    (seed : ExactBodyMap D.ModelBody {y : F | p y ≤ 1} (H v)) :
    ∃ out : C(closedHemisphere v, EuclideanSpace ℝ (Fin m) →L[ℝ] F),
      (∀ x, Function.Injective (out x) ∧ LinearMap.range (out x).toLinearMap = H x.val ∧
        out x '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H x.val : Set F)) ∧
      out (hemispherePole v) = seed.val := by
  letI : CompactSpace (sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  letI : CompactSpace (closedHemisphere v) :=
    isCompact_iff_compactSpace.mp (isCompact_closedHemisphere v)
  let init : C(closedHemisphere v, EuclideanSpace ℝ (Fin m) →L[ℝ] F) :=
    ContinuousMap.const _ seed.val
  obtain ⟨out, hout, hfix⟩ := D.exists_continuous_endpoint_section μ hp hC hProj
    (hemisphereContraction v) init (by intro x; simpa only [hemisphereContraction_zero] using seed.property)
  refine ⟨out, ?_, ?_⟩
  · simpa only [hemisphereContraction_one] using hout
  · exact hfix (hemispherePole v) (by intro t; simp only [hemisphereContraction_pole])

end BanachIsometric
