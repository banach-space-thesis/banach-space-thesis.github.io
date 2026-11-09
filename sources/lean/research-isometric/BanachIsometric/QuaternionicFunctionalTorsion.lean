import BanachIsometric.ExactSectionFiniteOrderRigidity
import BanachIsometric.QuaternionicFunctionalSetup
import BanachIsometric.QuaternionicCompletion

/-!
# Original right quaternionic Theorem A, conditional on the actual topology

This composes the actual hyperplane bundle, hemisphere clutching, finite-order
pullback construction, analytic signed degree, quadratic propagation, right
quaternionic reconstruction and diagonal gluing. The remaining compact-group
even-homotopy torsion theorem is an explicit argument, not an axiom or a claimed
proof. The ambient algebraic space receives no norm or topology, and its
original right action is retained as Module (Quaternion R)^op.
-/

noncomputable section
namespace BanachIsometric.Quaternionic

open Set Metric MeasureTheory
open scoped Quaternion Topology Topology.Homotopy NNReal

theorem HasHermitianSquare.pullback_injective
    {X Y : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [AddCommGroup Y] [Module Hᵐᵒᵖ Y]
    {p : X → ℝ} (hp : HasHermitianSquare p) (j : Y →ₗ[Hᵐᵒᵖ] X)
    (hj : Function.Injective j) : HasHermitianSquare (fun y => p (j y)) := by
  obtain ⟨h, hh, hpos⟩ := hp
  exact ⟨h.comap j, fun y => hh (j y), fun y hy =>
    hpos (j y) (fun hz => hy (hj (hz.trans j.map_zero.symm)))⟩

variable (hTorsion : ∀ (m : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S →
  ∀ k : ℕ, Even (k + 2) →
  ∀ α : HomotopyGroup (Fin (k + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion in
theorem standard_hermitianSquare_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) {p : HermitianAmbient n → ℝ}
    (hp : IsDefiniteHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : HermitianAmbient n) 1))
    (hSections : RealEquivalentSections n p) : HasHermitianSquare p := by
  obtain ⟨v, _hv₁, _hv₂⟩ := hyperplaneField_pair_coverage n hn 0 0
  obtain ⟨D⟩ := nonempty_functional_exactSectionPrincipalData volume hp hSphere hSections v
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties
    hp.standardAmbient_positiveHomogeneous hSphere
  let r := 4 * n + 1
  have hdim : Module.finrank ℝ (HermitianAmbient n) = r + 3 := by
    rw [finrank_real_euclidean]
    dsimp [r]
    omega
  have hEven : Even (Module.finrank ℝ (HermitianAmbient n)) := by
    rw [finrank_real_euclidean]
    exact ⟨2 * (n + 1), by omega⟩
  have hIndexEven : Even (4 * n + 2) := ⟨2 * n + 1, by omega⟩
  have hTor : ∀ α : HomotopyGroup (Fin (r + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α := by
    exact hTorsion (4 * n) D.ModelBody hS hreg h0 (4 * n) hIndexEven
  let e : HermitianAmbient n ≃L[ℝ] PiolaSpace (Module.finrank ℝ (HermitianAmbient n)) :=
    (stdOrthonormalBasis ℝ (HermitianAmbient n)).repr.toContinuousLinearEquiv |>.trans
      (euclideanCoordinates (Module.finrank ℝ (HermitianAmbient n)))
  obtain ⟨Q, _hQpos, hQ, _hbody⟩ := D.exists_ambient_quadraticForm_of_actual_homotopy_torsion
    volume hp.standardAmbient_positiveHomogeneous hSphere
    (hyperplaneField_projection_lipschitz n) (hyperplaneField_le_real_perp n)
    v r hdim hEven hTor e (hyperplaneField_pair_coverage n hn)
  exact hasHermitianSquare_of_realQuadratic hp Q hQ

include hTorsion in
theorem functionalStatement_of_body_even_homotopy_torsion
    {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] : FunctionalStatement (E := X) := by
  intro n p hn hdim hp hSphere hSections
  apply hasHermitianSquare_of_local (n + 1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using (Cardinal.natCast_add_one_le_iff).mpr hdim)
  intro Y hfinite hYdim
  letI : FiniteDimensional Hᵐᵒᵖ Y := hfinite
  have hYrank : Module.rank Hᵐᵒᵖ Y = ((n + 1 : ℕ) : Cardinal) := by
    rw [← Module.finrank_eq_rank, hYdim]
  obtain ⟨f, L, hL, hpf, hSf, _hD⟩ :=
    exists_functional_exactSectionSetup hp hSphere hSections Y hYrank volume
  have hfHerm := standard_hermitianSquare_of_body_even_homotopy_torsion
    hTorsion hn hpf hL.lipschitzOnWith hSf
  have hYHerm := hfHerm.pullback_injective f.symm.toLinearMap f.symm.injective
  simpa only [LinearEquiv.coe_toLinearMap, f.apply_symm_apply] using hYHerm

end BanachIsometric.Quaternionic


