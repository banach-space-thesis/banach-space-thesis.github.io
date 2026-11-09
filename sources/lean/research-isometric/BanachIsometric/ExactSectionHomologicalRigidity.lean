import BanachIsometric.ExactSectionHomologicalVanishing
import BanachIsometric.ExactSectionHomologicalAnalytic
import BanachIsometric.ExactSectionCanonicalMoments
import BanachIsometric.CanonicalSuspensionCount
import BanachIsometric.ExactSectionQuadraticPropagation

/-! Homological clutching of the actual exact-section bundle, followed by
the signed-moment calculation and the original pairwise propagation. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory SingularPrism
open scoped NNReal Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

theorem exists_reference_quadraticForm_of_homological_clutching
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C L : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : LipschitzWith L (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (n + 3)) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p (D.reference y) ^ 2 := by
  have hEquator : Even (n + 1) := by
    obtain ⟨j, hj⟩ := hEven
    exact ⟨j - 1, by omega⟩
  obtain ⟨K, hK⟩ := hp.exists_lipschitzWith hSphere
  let hcont := hK.continuous
  obtain ⟨c, hc, b, hb, hfill⟩ := D.exists_lipschitz_canonical_homological_lift_of_even_equator
    μ hp hSphere hProj v n hdim hEquator
  apply D.exists_reference_quadraticForm_of_lipschitz_canonical_lift
    μ hp hSphere hTangent v n hdim hEven hcont c hc b hb hfill
  intro k _
  apply ne_of_gt
  apply canonicalMoment_pos_of_interior_count hp hcont hSphere v n hdim _ k
  have h := ae_canonicalGaugeSuspensionConedChain_count_one hp hcont hSphere v n hdim
    (volume : Measure (Fin (n + 3) → ℝ))
  simpa only [canonicalGaugeSuspensionConedChain, canonicalMomentReferenceMap,
    canonicalHemisphereCoordinateProjection] using h

theorem exists_ambient_quadraticForm_of_homological_clutching
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C L : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : LipschitzWith L (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (n + 3)) (hpair : ∀ x y, ∃ a, x ∈ H a ∧ y ∈ H a) :
    ∃ Q : QuadraticForm ℝ F, Q.PosDef ∧ (∀ x, Q x = p x ^ 2) ∧
      {x | p x ≤ 1} = {x | Q x ≤ 1} := by
  obtain ⟨Q, _hQpos, hQ⟩ := D.exists_reference_quadraticForm_of_homological_clutching
    μ hp hSphere hProj hTangent v n hdim hEven
  obtain ⟨K, hK⟩ := hp.exists_lipschitzWith hSphere
  exact D.exists_ambient_quadraticForm_of_reference_quadraticForm hp hK.continuous Q hQ hpair

end BanachIsometric.ExactSectionPrincipalData
