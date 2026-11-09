import BanachIsometric.SmoothPullbackRegularization
import BanachIsometric.ExactSectionFiniteOrderRigidity

/-!
# An actual smooth positive-degree map with Lipschitz exact pullback operators

This gives the smooth-map regularity requested by the paper's annihilation
lemma, followed by its exact-operator regularization. The finite-order theorem
for the actual connected body group's homotopy remains an explicit input.
The smooth approximation preserves the actual signed degree by an actual
homotopy, and exact operators are transported along that same homotopy.
-/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal Manifold

theorem exists_smooth_positive_degree_exact_pullback_of_torsion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F}
    {a₀ : sphere (0 : F) 1} (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hTorsion : ∀ α : HomotopyGroup (Fin (n + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α)
    {N : ℕ} [NeZero N] (e : F ≃L[ℝ] PiolaSpace N) :
    letI : Fact (Module.finrank ℝ F = (n + 2) + 1) := ⟨hdim⟩
    ∃ ψ : C(sphere (0 : F) 1, sphere (0 : F) 1),
      ContMDiff (𝓡 (n + 2)) (𝓡 (n + 2)) (⊤ : ℕ∞) ψ ∧
      0 < continuousSphereSignedDegree e ψ ∧
      ∃ B : C(sphere (0 : F) 1, EuclideanSpace ℝ (Fin m) →L[ℝ] F), ∃ LB : ℝ≥0,
        LipschitzWith LB B ∧ ∀ a, Function.Injective (B a) ∧
          LinearMap.range (B a).toLinearMap = H (ψ a) ∧
          B a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (ψ a) : Set F) := by
  letI : Fact (Module.finrank ℝ F = (n + 2) + 1) := ⟨hdim⟩
  obtain ⟨φ, A, hdegree, hA⟩ := D.exists_positive_degree_exact_pullback_of_torsion
    μ hp hSphere hProj.continuous v n hdim hTorsion e
  obtain ⟨ψ, hsmooth, _Lψ, _hψ, _hclose, ⟨hom⟩, B, LB, hB, hBvalid⟩ :=
    D.exists_smooth_sphere_pullback_lipschitz_section (n := n + 2) μ hp hSphere hProj φ A hA
      (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨ψ, hsmooth, ?_, B, LB, hB, hBvalid⟩
  rwa [← continuousSphereSignedDegree_eq_of_homotopy e hom]

end BanachIsometric.ExactSectionPrincipalData
