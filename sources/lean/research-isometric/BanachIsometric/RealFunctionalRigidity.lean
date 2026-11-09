import BanachIsometric.HomologicalFunctionalRigidity
import BanachIsometric.RealEvenNormRigidity

/-! Real functional rigidity on the original algebraic space. In odd section
dimension, local Euclidean coordinates reduce the problem to homological
clutching. The even section dimensions use the tangent-field obstruction. -/

noncomputable section
namespace BanachIsometric

open Set Metric
open scoped Topology NNReal

theorem positiveGaugeData_of_real_odd_sections
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    {p : X → ℝ} (hp : AlgebraicPositiveHomogeneous p)
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hSphere : RealLocalSphereLipschitz n p) (hSections : RealEquivalentRealSections n p) :
    Nonempty (MetricGeometry.PositiveGaugeData p) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 2 * k + 3 := by
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j - 1, by omega⟩
  apply positiveGaugeData_of_local_quadratic hp (2 * k + 3 + 1) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hdim)
  intro Y hfinite hY
  letI : FiniteDimensional ℝ Y := hfinite
  obtain ⟨e, C, hC⟩ := hSphere Y hfinite hY
  let j : EuclideanSpace ℝ (Fin (2 * k + 3 + 1)) →ₗ[ℝ] X := Y.subtype.comp e.toLinearMap
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  obtain ⟨Q, _hQpos, hQ⟩ := real_odd_hyperplane_quadratic k (by simp)
    (hp.pullback j hj) hC (hSections.pullback j hj)
  refine ⟨Q.comp e.symm.toLinearMap, ?_⟩
  intro y
  change Q (e.symm y) = p y.val ^ 2
  rw [hQ]
  change p (e (e.symm y) : X) ^ 2 = _
  rw [e.apply_symm_apply]

theorem positiveGaugeData_of_real_sections
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    {p : X → ℝ} (hp : AlgebraicPositiveHomogeneous p)
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hSphere : RealLocalSphereLipschitz n p) (hSections : RealEquivalentRealSections n p) :
    Nonempty (MetricGeometry.PositiveGaugeData p) := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact positiveGaugeData_of_real_even_sections hp hn heven hdim hSphere hSections
  · have hn3 : 3 ≤ n := by obtain ⟨j, hj⟩ := hodd; omega
    exact positiveGaugeData_of_real_odd_sections hp hn3 hodd hdim hSphere hSections

theorem real_norm_positiveGaugeData
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ V)
    (hmetric : MetricSubspaceHomogeneity ℝ V n) :
    Nonempty (MetricGeometry.PositiveGaugeData (norm : V → ℝ)) := by
  apply positiveGaugeData_of_real_sections real_norm_algebraicPositiveHomogeneous
    hn hdim (real_norm_localSphereLipschitz n)
  intro E F hE hF
  letI : Module.Finite ℝ E := Module.finite_of_finrank_pos (by rw [hE]; omega)
  letI : Module.Finite ℝ F := Module.finite_of_finrank_pos (by rw [hF]; omega)
  obtain ⟨T⟩ := hmetric E F (by rw [← Module.finrank_eq_rank, hE]) (by rw [← Module.finrank_eq_rank, hF])
  let U := T.toRealLinearIsometryEquiv
  exact ⟨U.toLinearEquiv, fun x => U.norm_map x⟩

end BanachIsometric
