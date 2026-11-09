import BanachIsometric.ExactSectionHomologicalRigidity
import BanachIsometric.ComplexFunctionalTorsion
import BanachIsometric.QuaternionicFunctionalTorsion
import BanachIsometric.RealOddHyperplaneTorsion

/-! The geometric rigidity theorem applies to the same complex, quaternionic,
and real hyperplane fields as the original clutching proof. -/

noncomputable section
namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Quaternion NNReal

theorem complex_standard_hermitianSquare
    {n : ℕ} (hn : 2 ≤ n) {p : ComplexHermitianAmbient n → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : ComplexHermitianAmbient n) 1))
    (hSections : RealEquivalentSections n p) : HasHermitianSquare p := by
  let v : sphere (0 : ComplexHermitianAmbient n) 1 :=
    ⟨EuclideanSpace.single 0 1, by
      simp only [mem_sphere, dist_zero_right, EuclideanSpace.norm_single, norm_one]⟩
  obtain ⟨D⟩ := nonempty_complexFunctional_exactSectionPrincipalData volume hp hSphere hSections v
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hn
  let r := 2 * j + 3
  have hdim : Module.finrank ℝ (ComplexHermitianAmbient n) = r + 3 := by
    rw [complexHermitianAmbient_real_finrank]
    dsimp [r]
    omega
  have hEven : Even (r + 3) := ⟨j + 3, by dsimp [r]; omega⟩
  obtain ⟨Q, _hQpos, hQ, _hbody⟩ := D.exists_ambient_quadraticForm_of_homological_clutching
    volume hp.standardAmbient_positiveHomogeneous hSphere
    (complexHyperplaneField_projection_lipschitz n) (complexHyperplaneField_le_real_perp n)
    v r hdim hEven (complexHyperplaneField_pair_coverage n hn)
  exact hasHermitianSquare_of_realQuadratic hp Q hQ

/-- The complex case of Theorem A, using the original algebraic module and
the literal function and section equivalences in `ComplexFunctionalStatement`. -/
theorem complexTheoremA {X : Type*} [AddCommGroup X] [Module ℂ X] :
    ComplexFunctionalStatement (X := X) := by
  intro n p hn hdim hp hSphere hSections
  have hAvailable : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ X := by
    simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hdim
  apply hasHermitianSquare_of_local (n + 1) (by omega) hAvailable
  intro Y hfinite hYdim
  letI : FiniteDimensional ℂ Y := hfinite
  have hYrank : Module.rank ℂ Y = ((n + 1 : ℕ) : Cardinal) := by
    rw [← Module.finrank_eq_rank, hYdim]
  obtain ⟨f, L, hL, hpf, hSf, _⟩ :=
    exists_complexFunctional_exactSectionSetup hp hSphere hSections Y hYrank volume
  have hf := complex_standard_hermitianSquare hn hpf hL.lipschitzOnWith hSf
  simpa only [LinearEquiv.coe_toLinearMap, f.apply_symm_apply] using
    hf.pullback_injective f.symm.toLinearMap f.symm.injective

namespace Quaternionic

theorem standard_hermitianSquare
    {n : ℕ} (hn : 2 ≤ n) {p : HermitianAmbient n → ℝ}
    (hp : IsDefiniteHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : HermitianAmbient n) 1))
    (hSections : RealEquivalentSections n p) : HasHermitianSquare p := by
  obtain ⟨v, _hv₁, _hv₂⟩ := hyperplaneField_pair_coverage n hn 0 0
  obtain ⟨D⟩ := nonempty_functional_exactSectionPrincipalData volume hp hSphere hSections v
  let r := 4 * n + 1
  have hdim : Module.finrank ℝ (HermitianAmbient n) = r + 3 := by
    rw [finrank_real_euclidean]
    dsimp [r]
    omega
  have hEven : Even (r + 3) := ⟨2 * (n + 1), by dsimp [r]; omega⟩
  obtain ⟨Q, _hQpos, hQ, _hbody⟩ := D.exists_ambient_quadraticForm_of_homological_clutching
    volume hp.standardAmbient_positiveHomogeneous hSphere
    (hyperplaneField_projection_lipschitz n) (hyperplaneField_le_real_perp n)
    v r hdim hEven (hyperplaneField_pair_coverage n hn)
  exact hasHermitianSquare_of_realQuadratic hp Q hQ

/-- The quaternionic case of Theorem A, with the original right action
encoded by the opposite quaternion algebra. -/
theorem theoremA {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] : FunctionalStatement (E := X) := by
  intro n p hn hdim hp hSphere hSections
  apply hasHermitianSquare_of_local (n + 1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hdim)
  intro Y hfinite hYdim
  letI : FiniteDimensional Hᵐᵒᵖ Y := hfinite
  have hYrank : Module.rank Hᵐᵒᵖ Y = ((n + 1 : ℕ) : Cardinal) := by
    rw [← Module.finrank_eq_rank, hYdim]
  obtain ⟨f, L, hL, hpf, hSf, _⟩ :=
    exists_functional_exactSectionSetup hp hSphere hSections Y hYrank volume
  have hf := standard_hermitianSquare hn hpf hL.lipschitzOnWith hSf
  simpa only [LinearEquiv.coe_toLinearMap, f.apply_symm_apply] using
    hf.pullback_injective f.symm.toLinearMap f.symm.injective

end Quaternionic

theorem real_odd_hyperplane_quadratic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (k : ℕ) (hdim : Module.finrank ℝ V = 2 * k + 4) {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : V) 1))
    (hSections : RealEquivalentRealSections (2 * k + 3) p) :
    ∃ Q : QuadraticForm ℝ V, Q.PosDef ∧ ∀ x, Q x = p x ^ 2 := by
  have hpair : ∀ x y : V, ∃ a : sphere (0 : V) 1,
      x ∈ normalHyperplane a ∧ y ∈ normalHyperplane a := by
    intro x y
    obtain ⟨u, hu, hux, huy⟩ := exists_unit_normal_annihilating_pair (𝕜 := ℝ)
      (by rw [hdim]; omega) x y
    let a : sphere (0 : V) 1 := ⟨u, by simpa only [mem_sphere, dist_zero_right] using hu⟩
    exact ⟨a, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hux,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr huy⟩
  obtain ⟨v, _hv₁, _hv₂⟩ := hpair 0 0
  have hrank (a : sphere (0 : V) 1) : Module.finrank ℝ (normalHyperplane a) = 2 * k + 3 :=
    normalHyperplane_finrank (by omega) a
  have hEquivalent (a : sphere (0 : V) 1) : RealSectionEquivalent p (normalHyperplane v) (normalHyperplane a) := by
    obtain ⟨T, hT⟩ := hSections _ _ (hrank v) (hrank a)
    refine ⟨T, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change p (T x : V) ≤ 1
      rw [hT]
      exact hx
    · intro hy
      refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
      change p (T.symm y : V) ≤ 1
      rw [← hT, T.apply_symm_apply]
      exact hy
  obtain ⟨D⟩ := nonempty_exactSectionPrincipalData volume hp hSphere normalHyperplane
    lipschitzWith_normalHyperplane_projection
    (fun a => by simpa only [finrank_euclideanSpace_fin] using hrank a) v hEquivalent
  have hEven : Even ((2 * k + 1) + 3) := ⟨k + 2, by omega⟩
  obtain ⟨Q, hQpos, hQ, _⟩ := D.exists_ambient_quadraticForm_of_homological_clutching
    volume hp hSphere lipschitzWith_normalHyperplane_projection (fun _ => le_rfl)
    v (2 * k + 1) (by omega) hEven hpair
  exact ⟨Q, hQpos, hQ⟩

end BanachIsometric
