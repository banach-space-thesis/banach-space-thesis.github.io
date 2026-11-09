import BanachIsometric.TotallyDisconnectedHomotopy
import BanachIsometric.ExactSectionFiniteOrderRigidity

/-! Actual triviality of the identity-component homotopy groups discharges
the topological obligation for totally disconnected, in particular finite,
body structure groups. No homotopy-torsion premise remains in these cases. -/

namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {m : ℕ} {p : F → ℝ}
  {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

omit [FiniteDimensional ℝ F] in
theorem homotopy_torsion_of_totallyDisconnected_structureGroup
    (D : ExactSectionPrincipalData m p H a₀) [TotallyDisconnectedSpace D.StructureGroup]
    (n : ℕ) (α : HomotopyGroup (Fin (n + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1) : IsOfFinOrder α :=
  isOfFinOrder_homotopyGroup_identityComponent_of_totallyDisconnected α

theorem exists_reference_quadraticForm_of_totallyDisconnected_structureGroup
    (D : ExactSectionPrincipalData m p H a₀) [TotallyDisconnectedSpace D.StructureGroup]
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (Module.finrank ℝ F))
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F)) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p (D.reference y) ^ 2 :=
  D.exists_reference_quadraticForm_of_actual_homotopy_torsion μ hp hSphere hProj hTangent
    v n hdim hEven (D.homotopy_torsion_of_totallyDisconnected_structureGroup n) e

theorem exists_ambient_quadraticForm_of_totallyDisconnected_structureGroup
    (D : ExactSectionPrincipalData m p H a₀) [TotallyDisconnectedSpace D.StructureGroup]
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (Module.finrank ℝ F))
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F))
    (hpair : ∀ x y, ∃ a, x ∈ H a ∧ y ∈ H a) :
    ∃ Q : QuadraticForm ℝ F, Q.PosDef ∧ (∀ x, Q x = p x ^ 2) ∧
      {x | p x ≤ 1} = {x | Q x ≤ 1} :=
  D.exists_ambient_quadraticForm_of_actual_homotopy_torsion μ hp hSphere hProj hTangent
    v n hdim hEven (D.homotopy_torsion_of_totallyDisconnected_structureGroup n) e hpair

theorem exists_reference_quadraticForm_of_finite_structureGroup
    (D : ExactSectionPrincipalData m p H a₀) [Finite D.StructureGroup]
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (Module.finrank ℝ F))
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F)) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p (D.reference y) ^ 2 :=
  D.exists_reference_quadraticForm_of_totallyDisconnected_structureGroup
    μ hp hSphere hProj hTangent v n hdim hEven e

theorem exists_ambient_quadraticForm_of_finite_structureGroup
    (D : ExactSectionPrincipalData m p H a₀) [Finite D.StructureGroup]
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hEven : Even (Module.finrank ℝ F))
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F))
    (hpair : ∀ x y, ∃ a, x ∈ H a ∧ y ∈ H a) :
    ∃ Q : QuadraticForm ℝ F, Q.PosDef ∧ (∀ x, Q x = p x ^ 2) ∧
      {x | p x ≤ 1} = {x | Q x ≤ 1} :=
  D.exists_ambient_quadraticForm_of_totallyDisconnected_structureGroup
    μ hp hSphere hProj hTangent v n hdim hEven e hpair

end BanachIsometric.ExactSectionPrincipalData
