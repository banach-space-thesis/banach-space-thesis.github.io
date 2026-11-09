import BanachIsometric.ExactSectionFiniteOrderRigidity
import BanachIsometric.ComplexFunctionalSetup
import BanachIsometric.HermitianGluing

/-!
# Original complex functional hypotheses, with the remaining topology explicit

This file composes the entire constructed bundle, actual signed degree,
polynomial rigidity, original scalar reconstruction and algebraic gluing.
Its input `hTorsion` is precisely a still-unproved topological assertion about
the ACTUAL even homotopy groups of compact body automorphism groups. Thus the
last theorem is an implication to Theorem A, not an unconditional proof of A.

The ambient algebraic complex space receives no norm or topology. The real
section maps are not required to be complex-linear. The indicated alternative
global proof glues actual local Hermitian forms by their common polarization.
-/

noncomputable section
namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

theorem HasHermitianSquare.pullback_injective
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {p : X → ℝ} (hp : HasHermitianSquare p) (j : Y →ₗ[ℂ] X)
    (hj : Function.Injective j) : HasHermitianSquare (fun y => p (j y)) := by
  obtain ⟨h, hh⟩ := hp
  refine ⟨{
    form := fun x y => h.form (j x) (j y)
    conj_symm := fun x y => h.conj_symm (j x) (j y)
    add_right := ?_
    smul_right := ?_
    self_im := fun x => h.self_im (j x)
    self_nonneg := fun x => h.self_nonneg (j x)
    self_pos := fun x hx => h.self_pos (j x) (fun he => hx (hj (he.trans j.map_zero.symm)))
  }, fun x => hh (j x)⟩
  · intro x y z
    rw [j.map_add]
    exact h.add_right (j x) (j y) (j z)
  · intro x y a
    rw [j.map_smul]
    exact h.smul_right (j x) (j y) a

variable (hTorsion : ∀ (m : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))),
  IsCompact S → closure (interior S) = S →
  (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S →
  ∀ k : ℕ, Even (k + 2) →
  ∀ α : HomotopyGroup (Fin (k + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

theorem complex_standard_hermitianSquare_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 2 ≤ n) {p : ComplexHermitianAmbient n → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : ComplexHermitianAmbient n) 1))
    (hSections : RealEquivalentSections n p) : HasHermitianSquare p := by
  let v : sphere (0 : ComplexHermitianAmbient n) 1 :=
    ⟨EuclideanSpace.single 0 1, by
      simp only [mem_sphere, dist_zero_right, EuclideanSpace.norm_single, norm_one]⟩
  obtain ⟨D⟩ := nonempty_complexFunctional_exactSectionPrincipalData volume hp hSphere hSections v
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties
    hp.standardAmbient_positiveHomogeneous hSphere
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hn
  let r := 2 * j + 3
  have hdim : Module.finrank ℝ (ComplexHermitianAmbient n) = r + 3 := by
    rw [complexHermitianAmbient_real_finrank]
    dsimp [r]
    omega
  have hEven : Even (Module.finrank ℝ (ComplexHermitianAmbient n)) := by
    rw [complexHermitianAmbient_real_finrank]
    exact ⟨n + 1, by omega⟩
  have hIndexEven : Even (2 * j + 2 + 2) := ⟨j + 2, by omega⟩
  have hTor : ∀ α : HomotopyGroup (Fin (r + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α := by
    exact hTorsion (2 * n) D.ModelBody hS hreg h0 (2 * j + 2) hIndexEven
  let e : ComplexHermitianAmbient n ≃L[ℝ]
      PiolaSpace (Module.finrank ℝ (ComplexHermitianAmbient n)) :=
    (stdOrthonormalBasis ℝ (ComplexHermitianAmbient n)).repr.toContinuousLinearEquiv |>.trans
      (euclideanCoordinates (Module.finrank ℝ (ComplexHermitianAmbient n)))
  obtain ⟨Q, _hQpos, hQ, _hbody⟩ := D.exists_ambient_quadraticForm_of_actual_homotopy_torsion
    volume hp.standardAmbient_positiveHomogeneous hSphere
    (complexHyperplaneField_projection_lipschitz n) (complexHyperplaneField_le_real_perp n)
    v r hdim hEven hTor e (complexHyperplaneField_pair_coverage n hn)
  exact hasHermitianSquare_of_realQuadratic hp Q hQ

theorem complexFunctionalStatement_of_body_even_homotopy_torsion
    {X : Type*} [AddCommGroup X] [Module ℂ X] : ComplexFunctionalStatement (X := X) := by
  intro n p hn hdim hp hSphere hSections
  have hAvailable : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ X := by
    simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hdim
  apply hasHermitianSquare_of_local (n + 1) (by omega) hAvailable
  intro Y hfinite hYdim
  letI : FiniteDimensional ℂ Y := hfinite
  have hYrank : Module.rank ℂ Y = ((n + 1 : ℕ) : Cardinal) := by
    rw [← Module.finrank_eq_rank, hYdim]
  obtain ⟨f, L, hL, hpf, hSf, _hD⟩ :=
    exists_complexFunctional_exactSectionSetup hp hSphere hSections Y hYrank volume
  have hfHerm := complex_standard_hermitianSquare_of_body_even_homotopy_torsion
    hTorsion hn hpf hL.lipschitzOnWith hSf
  have hYHerm := hfHerm.pullback_injective f.symm.toLinearMap f.symm.injective
  simpa only [LinearEquiv.coe_toLinearMap, f.apply_symm_apply] using hYHerm

end BanachIsometric
