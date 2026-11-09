import BanachIsometric.ConnectedHemisphereClutching
import BanachIsometric.FiniteOrderPositiveDegreeSection
import BanachIsometric.ExactSectionQuadraticPropagation

/-!
# The original exact-section bundle and its actual homotopy obstruction

Hemisphere frames, the based connected-group clutching map, a positive-degree
pullback map, its actual exact operators, and the reference ellipsoid are all
constructed here from the original bundle data. The sole additional topological
premise is displayed as torsion of the ACTUAL homotopy group of its identity
structure group. The compact Lie group theorem needed to discharge that premise
is a separate, still unfinished theorem; this file does not assert Theorem 4.1
unconditionally.

The final propagation uses the original atlas and pair coverage instead of
normal-map surjectivity. The positive degree is the proved analytic signed degree
of the same suspended map that carries the pullback section.
-/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory SphereGenerator
open scoped Topology Topology.Homotopy NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {m : ℕ} {p : F → ℝ}
  {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

theorem exists_positive_degree_exact_pullback_of_torsion
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hTorsion : ∀ α : HomotopyGroup (Fin (n + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α)
    {N : ℕ} [NeZero N] (e : F ≃L[ℝ] PiolaSpace N) :
    ∃ φ : C(sphere (0 : F) 1, sphere (0 : F) 1),
    ∃ B : C(sphere (0 : F) 1, EuclideanSpace ℝ (Fin m) →L[ℝ] F),
      0 < continuousSphereSignedDegree e φ ∧
      ∀ a, Function.Injective (B a) ∧ LinearMap.range (B a).toLinearMap = H (φ a) ∧
        B a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (φ a) : Set F) := by
  let L := equatorStandardLinearIsometry v (n + 1) hdim
  have horth : Module.finrank ℝ (ℝ ∙ v.val)ᗮ = n + 2 := by
    simpa only [finrank_euclideanSpace_fin] using L.toLinearEquiv.finrank_eq
  have hrank : 1 < Module.rank ℝ (ℝ ∙ v.val)ᗮ := by
    rw [← Module.finrank_eq_rank, horth]
    exact_mod_cast (by omega : 1 < n + 2)
  let eQ := equatorStandardSphereHomeomorph v (n + 1) hdim
  obtain ⟨north, south, g, hnorth, hsouth, hg, hglue⟩ :=
    D.exists_connected_hemisphere_clutching μ hp hSphere hProj v hrank
      (eQ.symm (sphereBasepoint (n + 1)))
  obtain ⟨_d, _hd, φ, B, _LB, _hLip, _hDegree, _hContinuous, hpos, hB⟩ :=
    exists_positive_degree_exact_pullback_section_of_finiteOrder e v n hdim
      north south hnorth hsouth g hglue hg (hTorsion _)
  exact ⟨φ, B, hpos, hB⟩

theorem exists_reference_quadraticForm_of_actual_homotopy_torsion
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (Module.finrank ℝ F))
    (hTorsion : ∀ α : HomotopyGroup (Fin (n + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α)
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F)) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p (D.reference y) ^ 2 := by
  letI : NeZero (Module.finrank ℝ F) := ⟨by omega⟩
  obtain ⟨φ, B, hpos, hB⟩ := D.exists_positive_degree_exact_pullback_of_torsion
    μ hp hSphere hProj.continuous v n hdim hTorsion e
  exact D.exists_reference_quadraticForm_of_nonzero_pullback_section
    μ hp hSphere hProj hTangent φ B hB e hEven (ne_of_gt hpos)

theorem exists_ambient_quadraticForm_of_actual_homotopy_torsion
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (Module.finrank ℝ F))
    (hTorsion : ∀ α : HomotopyGroup (Fin (n + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α)
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F))
    (hpair : ∀ x y, ∃ a, x ∈ H a ∧ y ∈ H a) :
    ∃ Q : QuadraticForm ℝ F, Q.PosDef ∧ (∀ x, Q x = p x ^ 2) ∧
      {x | p x ≤ 1} = {x | Q x ≤ 1} := by
  obtain ⟨Q, _hQpos, hQ⟩ := D.exists_reference_quadraticForm_of_actual_homotopy_torsion
    μ hp hSphere hProj hTangent v n hdim hEven hTorsion e
  obtain ⟨L, hL⟩ := hp.exists_lipschitzWith hSphere
  exact D.exists_ambient_quadraticForm_of_reference_quadraticForm hp hL.continuous Q hQ hpair

end BanachIsometric.ExactSectionPrincipalData
