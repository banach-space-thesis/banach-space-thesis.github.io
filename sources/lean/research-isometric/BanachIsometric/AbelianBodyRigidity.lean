import BanachIsometric.AbelianBodyHomotopy
import BanachIsometric.ExactSectionFiniteOrderRigidity

/-! The actual abelian identity-component case of section rigidity has no
homotopy-torsion assumption. Its higher homotopy vanishing is proved through
the constructed finite-moment stabilizer and its actual exponential cover. -/

namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {m : ℕ} {p : F → ℝ}
  {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

theorem actual_homotopy_torsion_of_abelian_identityComponent
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hAbelian : ∀ R T : Subgroup.connectedComponentOfOne D.StructureGroup, R * T = T * R)
    (n : ℕ) (α : HomotopyGroup (Fin (n + 2))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1) : IsOfFinOrder α := by
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hSphere
  exact isOfFinOrder_higherHomotopy_bodyIdentityComponent_of_abelian
    μ D.ModelBody hS hreg h0 hAbelian n α

theorem exists_reference_quadraticForm_of_abelian_identityComponent
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (k : ℕ) (hdim : Module.finrank ℝ F = 2 * k + 4)
    (hAbelian : ∀ R T : Subgroup.connectedComponentOfOne D.StructureGroup, R * T = T * R)
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F)) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p (D.reference y) ^ 2 := by
  have hEven : Even (Module.finrank ℝ F) := by rw [hdim]; exact ⟨k + 2, by omega⟩
  have hTor : ∀ α : HomotopyGroup (Fin ((2 * k + 1) + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α :=
    D.actual_homotopy_torsion_of_abelian_identityComponent μ hp hSphere hAbelian (2 * k)
  exact D.exists_reference_quadraticForm_of_actual_homotopy_torsion
    μ hp hSphere hProj hTangent v (2 * k + 1) (by omega) hEven hTor e

theorem exists_ambient_quadraticForm_of_abelian_identityComponent
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (v : sphere (0 : F) 1) (k : ℕ) (hdim : Module.finrank ℝ F = 2 * k + 4)
    (hAbelian : ∀ R T : Subgroup.connectedComponentOfOne D.StructureGroup, R * T = T * R)
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F))
    (hpair : ∀ x y, ∃ a, x ∈ H a ∧ y ∈ H a) :
    ∃ Q : QuadraticForm ℝ F, Q.PosDef ∧ (∀ x, Q x = p x ^ 2) ∧
      {x | p x ≤ 1} = {x | Q x ≤ 1} := by
  have hEven : Even (Module.finrank ℝ F) := by rw [hdim]; exact ⟨k + 2, by omega⟩
  have hTor : ∀ α : HomotopyGroup (Fin ((2 * k + 1) + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α :=
    D.actual_homotopy_torsion_of_abelian_identityComponent μ hp hSphere hAbelian (2 * k)
  exact D.exists_ambient_quadraticForm_of_actual_homotopy_torsion
    μ hp hSphere hProj hTangent v (2 * k + 1) (by omega) hEven hTor e hpair

end BanachIsometric.ExactSectionPrincipalData
