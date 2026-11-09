import BanachIsometric.RealEvenHyperplaneRigidity
import BanachIsometric.RealOddFunctionalTorsion

/-! Norm-free real even-section functional rigidity. Arbitrary local real
Euclidean coordinates are used only on finite-dimensional subspaces, and the
actual local quadratic forms glue algebraically on the original vector space.
The real even-dimensional branch has no external homotopy-torsion premise. -/

namespace BanachIsometric

open Set Metric
open scoped Topology NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

theorem positiveGaugeData_of_real_even_sections
    {p : X → ℝ} (hp : AlgebraicPositiveHomogeneous p)
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hSphere : RealLocalSphereLipschitz n p) (hSections : RealEquivalentRealSections n p) :
    Nonempty (MetricGeometry.PositiveGaugeData p) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 2 * k + 2 := by
    obtain ⟨j, hj⟩ := heven
    exact ⟨j - 1, by omega⟩
  apply positiveGaugeData_of_local_quadratic hp (2 * k + 2 + 1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hdim)
  intro Y hfinite hY
  letI : FiniteDimensional ℝ Y := hfinite
  obtain ⟨e, C, hC⟩ := hSphere Y hfinite hY
  let j : EuclideanSpace ℝ (Fin (2 * k + 2 + 1)) →ₗ[ℝ] X := Y.subtype.comp e.toLinearMap
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  have hpj := hp.pullback j hj
  have hSj := hSections.pullback j hj
  obtain ⟨Q, _hQpos, hQ⟩ := real_even_hyperplane_quadratic k (by simp) hpj hC hSj
  refine ⟨Q.comp e.symm.toLinearMap, ?_⟩
  intro y
  change Q (e.symm y) = p y.val ^ 2
  rw [hQ]
  change p (e (e.symm y) : X) ^ 2 = _
  rw [e.apply_symm_apply]

theorem real_even_quadratic
    {p : X → ℝ} (hp : AlgebraicPositiveHomogeneous p)
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hSphere : RealLocalSphereLipschitz n p) (hSections : RealEquivalentRealSections n p) :
    ∃ Q : QuadraticForm ℝ X, Q.PosDef ∧ ∀ x, Q x = p x ^ 2 := by
  obtain ⟨D⟩ := positiveGaugeData_of_real_even_sections hp hn heven hdim hSphere hSections
  exact ⟨D.quadraticForm, D.quadraticForm_posDef, D.quadraticForm_diagonal⟩

end
end BanachIsometric
