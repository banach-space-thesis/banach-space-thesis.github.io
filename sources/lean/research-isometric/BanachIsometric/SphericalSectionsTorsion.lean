import BanachIsometric.SmoothSphereLipschitz
import BanachIsometric.ExactSectionFiniteOrderRigidity
import BanachIsometric.RadialStarBody

/-!
# Spherical sections of the literal original radial body

The whole constructed bundle and analytic argument now give the section and
ambient conclusions from a C-one orthogonal-projection field. The global
projection Lipschitz bound is derived. This is the smooth projection-field
formulation of the paper's spherical-sections theorem, conditional only on the
explicit actual body-group even-homotopy torsion assertion.

Mathlib at this revision has no smooth Grassmannian manifold implementation.
This file therefore does not assert a formal equivalence with a separate
Grassmannian-manifold predicate. It states the precise smooth projection
criterion used by the proof, rather than hiding that interface distinction.
-/

noncomputable section
namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal Manifold

theorem RadialStarBody.spherical_sections_quadratic_of_body_even_homotopy_torsion
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Nontrivial V] (K : RadialStarBody V) {C : ℝ≥0} (hK : LipschitzWith C K.radius)
    (k : ℕ) (hdim : Module.finrank ℝ V = 2 * k + 4)
    (H : sphere (0 : V) 1 → Submodule ℝ V)
    (hSmooth : letI : Fact (Module.finrank ℝ V = (2 * k + 3) + 1) := ⟨hdim⟩
      ContMDiff (𝓡 (2 * k + 3)) 𝓘(ℝ, V →L[ℝ] V) 1
        (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (m : ℕ) (hrank : ∀ a, Module.finrank ℝ (H a) = m)
    (v : sphere (0 : V) 1)
    (hEquivalent : ∀ a, RealSectionEquivalent K.gauge (H v) (H a))
    (hTorsion : ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))),
      IsCompact S → closure (interior S) = S →
      (0 : EuclideanSpace ℝ (Fin d)) ∈ interior S →
      ∀ j : ℕ, Even (j + 2) →
      ∀ α : HomotopyGroup (Fin (j + 2))
        (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α) :
    (∀ a, ∃ Q : QuadraticForm ℝ (H a), Q.PosDef ∧
      (∀ y, Q y = K.gauge y.val ^ 2) ∧
      {y : H a | y.val ∈ K.carrier} = {y | Q y ≤ 1}) ∧
    ((∀ x y : V, ∃ a, x ∈ H a ∧ y ∈ H a) →
      ∃ Q : QuadraticForm ℝ V, Q.PosDef ∧ (∀ x, Q x = K.gauge x ^ 2) ∧
        K.carrier = {x | Q x ≤ 1}) := by
  letI : Fact (Module.finrank ℝ V = (2 * k + 3) + 1) := ⟨hdim⟩
  obtain ⟨LP, hProj⟩ := ContMDiff.exists_lipschitzWith_sphere hSmooth
  obtain ⟨LG, hGauge⟩ := K.exists_gauge_sphere_lipschitz hK
  obtain ⟨D⟩ := nonempty_exactSectionPrincipalData volume K.gauge_homogeneous hGauge H hProj
    (fun a => by simpa only [finrank_euclideanSpace_fin] using hrank a) v hEquivalent
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties K.gauge_homogeneous hGauge
  have hEven : Even (Module.finrank ℝ V) := by rw [hdim]; exact ⟨k + 2, by omega⟩
  have hIndexEven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
  have hTor : ∀ α : HomotopyGroup (Fin ((2 * k + 1) + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α :=
    hTorsion m D.ModelBody hS hreg h0 (2 * k) hIndexEven
  let e : V ≃L[ℝ] PiolaSpace (Module.finrank ℝ V) :=
    (stdOrthonormalBasis ℝ V).repr.toContinuousLinearEquiv |>.trans
      (euclideanCoordinates (Module.finrank ℝ V))
  obtain ⟨Q, _hQpos, hQ⟩ := D.exists_reference_quadraticForm_of_actual_homotopy_torsion
    volume K.gauge_homogeneous hGauge hProj hTangent v (2 * k + 1)
    (by omega) hEven hTor e
  refine ⟨?_, ?_⟩
  · intro a
    obtain ⟨R, hRpos, hR, hRbody⟩ :=
      D.exists_section_quadraticForm_of_reference_quadraticForm K.gauge_homogeneous Q hQ a
    refine ⟨R, hRpos, hR, ?_⟩
    simpa only [K.carrier_eq_sublevel, mem_setOf_eq] using hRbody
  · intro hpair
    obtain ⟨R, hRpos, hR, hRbody⟩ := D.exists_ambient_quadraticForm_of_reference_quadraticForm
      K.gauge_homogeneous (K.exists_gauge_lipschitz hK).choose_spec.continuous Q hQ hpair
    exact ⟨R, hRpos, hR, K.carrier_eq_sublevel.trans hRbody⟩

end BanachIsometric
