import BanachIsometric.RealOddHyperplaneTorsion
import BanachIsometric.RealQuadraticGluing

/-! Algebraic real odd-section functional rigidity, conditional only on the
same actual compact-body even-homotopy torsion theorem. No norm or topology
is assigned to the original X; local Euclidean coordinates are arbitrary
real-linear coordinates, and the local quadratic forms glue by polarization. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

noncomputable section

variable {X V : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]

theorem RealEquivalentRealSections.pullback {n : ℕ} {p : X → ℝ}
    (h : RealEquivalentRealSections n p) (j : V →ₗ[ℝ] X) (hj : Function.Injective j) :
    RealEquivalentRealSections n (fun v => p (j v)) := by
  intro E F hE hF
  let eE := Submodule.equivMapOfInjective j hj E
  let eF := Submodule.equivMapOfInjective j hj F
  obtain ⟨T, hT⟩ := h (E.map j) (F.map j) (eE.finrank_eq.symm.trans hE) (eF.finrank_eq.symm.trans hF)
  let U := eE.trans (T.trans eF.symm)
  have hval (x : E) : j (U x : V) = (T (eE x) : X) :=
    congrArg Subtype.val (eF.apply_symm_apply (T (eE x)))
  refine ⟨U, ?_⟩
  intro x
  change p (j (U x : V)) = p (j (x : V))
  rw [hval]
  exact hT (eE x)

def RealLocalSphereLipschitz (n : ℕ) (p : X → ℝ) : Prop :=
  ∀ Y : Submodule ℝ X, FiniteDimensional ℝ Y → Module.finrank ℝ Y = n + 1 →
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] Y, ∃ C : ℝ≥0,
      LipschitzOnWith C (fun v => p (e v : X)) (sphere 0 1)

variable (hTorsion : ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin d)) ∈ interior S →
  ∀ j : ℕ, Even (j + 2) →
  ∀ α : HomotopyGroup (Fin (j + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

theorem positiveGaugeData_of_real_odd_sections_of_body_even_homotopy_torsion
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
  have hpj := hp.pullback j hj
  have hSj := hSections.pullback j hj
  obtain ⟨Q, _hQpos, hQ⟩ := real_odd_hyperplane_quadratic_of_body_even_homotopy_torsion hTorsion
    k (by simp) hpj hC hSj
  refine ⟨Q.comp e.symm.toLinearMap, ?_⟩
  intro y
  change Q (e.symm y) = p y.val ^ 2
  rw [hQ]
  change p (e (e.symm y) : X) ^ 2 = _
  rw [e.apply_symm_apply]

theorem real_odd_quadratic_of_body_even_homotopy_torsion
    {p : X → ℝ} (hp : AlgebraicPositiveHomogeneous p)
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hSphere : RealLocalSphereLipschitz n p) (hSections : RealEquivalentRealSections n p) :
    ∃ Q : QuadraticForm ℝ X, Q.PosDef ∧ ∀ x, Q x = p x ^ 2 := by
  obtain ⟨D⟩ := positiveGaugeData_of_real_odd_sections_of_body_even_homotopy_torsion
    hTorsion hp hn hodd hdim hSphere hSections
  exact ⟨D.quadraticForm, D.quadraticForm_posDef, D.quadraticForm_diagonal⟩

end
end BanachIsometric
