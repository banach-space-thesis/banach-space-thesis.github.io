import ThesisCommon.Analysis.ALFragmentGeometricPartition
import ThesisCommon.Analysis.FiniteTopologicalDensity

/-! Atomless fragments have infinite principal density. Conversely, a
homogeneous fragment of finite density is a genuine positive lattice atom. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
  [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  {e : E} [Fact (0 ≤ e)]
include hAL

theorem aleph0_le_principalDensity_of_atomless_positiveFragment
    (a : PositiveFragmentAlgebra e) (hne : a ≠ ⊥)
    (ha : NoPositiveAtomsBelow (positiveFragmentValue a)) :
    Cardinal.aleph0 ≤ principalDensity a := by
  obtain ⟨p, hple, hd, hnorm, _⟩ := exists_positiveFragment_geometric_partition hAL a ha
  have hapos : 0 < ‖positiveFragmentValue a‖ := norm_pos_iff.mpr (by
    intro hz
    exact hne ((positiveFragmentValue_injective e) (by simpa using hz)))
  have hpne (n : ℕ) : p n ≠ ⊥ := by
    intro hz
    have hpos : 0 < ‖positiveFragmentValue (p n)‖ := by rw [hnorm]; positivity
    simpa [hz] using hpos
  let j : ℕ → Iic a := fun n => ⟨p n, hple n⟩
  have hj : Function.Injective j := by
    intro m n heq
    by_contra hne
    have hp : p m = p n := congrArg Subtype.val heq
    have hdis := hd hne
    change Disjoint (p m) (p n) at hdis
    rw [hp] at hdis
    exact hpne n (disjoint_self.mp hdis)
  letI : Infinite (Iic a) := Infinite.of_injective j hj
  exact aleph0_le_topologicalDensity_of_infinite (Iic a)

theorem isPositiveLatticeAtom_of_isAtom_positiveFragment
    (a : PositiveFragmentAlgebra e) (ha : IsAtom a) :
    IsPositiveLatticeAtom (positiveFragmentValue a) := by
  by_contra hnot
  have hne : positiveFragmentValue a ≠ 0 := by
    intro hz
    exact ha.1 ((positiveFragmentValue_injective e) (by simpa using hz))
  obtain ⟨y, hy, hyne, hyne_a⟩ := al_exists_nontrivial_fragment hAL
    (positiveFragmentValue_nonneg a) hne hnot
  let b : PositiveFragmentAlgebra e := positiveFragmentOf
    (hy.trans (positiveFragmentValue_isFragment a))
  have hba : b ≤ a := hy.2.1
  have hb : b ≠ ⊥ := by
    intro hz
    have := congrArg positiveFragmentValue hz
    exact hyne (by simpa [b] using this)
  have heq : b = a := (ha.le_iff_eq hb).mp hba
  exact hyne_a (congrArg positiveFragmentValue heq)

theorem isPositiveLatticeAtom_of_homogeneous_finite_density
    (a : PositiveFragmentAlgebra e) (ha : IsDensityHomogeneous a)
    (h : principalDensity a < Cardinal.aleph0) :
    IsPositiveLatticeAtom (positiveFragmentValue a) :=
  isPositiveLatticeAtom_of_isAtom_positiveFragment hAL a
    (ha.isAtom_of_principalDensity_lt_aleph0 h)

end ThesisCommon
