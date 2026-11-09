import PL1.BalancedFragmentTree
import PL1.LatticeFragments
import PL1.LatticeRademacherWeak

/-!
# Separable Schur Banach lattices are atomic and have RNP

An atomless positive fragment produces a genuine balanced binary tree. Its
Rademachers have constant lattice modulus and satisfy the actual square bound
on every finite subsequence, contradicting the Schur property. Atomic bands
then supply the unconditional finite-dimensional projections required for RNP.
-/

noncomputable section
open scoped Topology BigOperators
universe u v

namespace PL1.SchurLattice

variable {E : Type u} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- The actual balanced tree satisfies the square estimate on every finite
family of distinct Rademacher indices, with no subsequence restriction. -/
theorem balancedTree_rademacherSquareBound (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ)
    {u : E} {split : E → E} (hu : 0 ≤ u)
    (hs : BalancedFragmentTree.IsBalancedSplit φ u split) :
    HasRademacherSquareBound φ u (BalancedFragmentTree.rademacher u split) := by
  classical
  intro N q hq ε hε
  let m := (Finset.univ.sup q) + 1
  have hqm (i : Fin N) : q i < m :=
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  let f : Fin N → Fin m := fun i => ⟨q i, hqm i⟩
  have hf : Function.Injective f := fun i j hij => hq (congrArg Fin.val hij)
  have hσ (i j : Fin N) :
      (∑ w : BalancedFragmentTree.Word m,
        φ (BalancedFragmentTree.cell u split m w) * BalancedFragmentTree.sign (f i) w *
          BalancedFragmentTree.sign (f j) w) = if i = j then φ u else 0 := by
    simpa only [hf.eq_iff] using BalancedFragmentTree.weighted_sign_orthogonality hu hs (f i) (f j)
  have h := dual_abs_sum_sq_le_of_orthogonal_fragments φ hφ u
    (BalancedFragmentTree.cell u split m)
    (fun w => (BalancedFragmentTree.cell_mem_Icc hu hs m w).1)
    (BalancedFragmentTree.cell_pairwise_disjoint hu hs m)
    (BalancedFragmentTree.sum_cell u split m)
    (fun i : Fin N => BalancedFragmentTree.rademacher u split (q i))
    (fun i w => BalancedFragmentTree.sign (f i) w)
    (fun i => BalancedFragmentTree.rademacher_refinement u split (hqm i)) hσ ε
  have hεsq (i : Fin N) : ε i ^ 2 = 1 := by
    rcases hε i with hi | hi <;> simp [hi]
  simpa only [hεsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using h

/-- Separability, completeness and the Schur property suffice for actual
vector-lattice atomicity; it is no longer an additional premise. -/
theorem isAtomicLattice_of_schur [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (hS : HasSchurProperty ℝ E) : IsAtomicLattice E := by
  obtain ⟨φ, hφpos, hφ⟩ := exists_strictlyPositive (E := E)
  intro u hu
  by_contra hbad
  have hna : ∀ a : E, IsLatticeAtom a → ¬ a ≤ u := fun a ha hau => hbad ⟨a, ha, hau⟩
  obtain ⟨split, hs⟩ := BalancedFragmentTree.exists_balancedSplit φ u (by
    intro x hx hxu
    exact LatticeFragments.exists_half_fragment hS φ hφ hx
      (fun a ha hax => hna a ha (hax.trans hxu)))
  have heq : u = 0 := eq_zero_of_constant_abs_rademacherSquareBound hS φ hφ u
    (BalancedFragmentTree.rademacher u split)
    (BalancedFragmentTree.abs_rademacher hu.le hs)
    (balancedTree_rademacherSquareBound φ hφpos hu.le hs)
  exact hu.ne' heq

/-- Full vector-measure RNP for every separable Schur Banach lattice, with
an independent universe for the source measure space. -/
theorem hasRadonNikodymProperty_of_schur [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (hS : HasSchurProperty ℝ E) : HasRadonNikodymProperty.{u, v} E :=
  AtomicBandDecomposition.hasRadonNikodymProperty_of_atomic hS (isAtomicLattice_of_schur hS)

end PL1.SchurLattice
