import PL1.LatticeReduction
import PL1.SchurLatticeAtomicity

/-!
# The full reviewed Theorem A

The actual Schur counterexample admits no equivalent real Banach-lattice
structure: separable Schur Banach lattices have the full vector-measure RNP,
whereas this complemented range does not. The complex endpoint retains the
reviewed, stronger prohibition on its underlying real space.
-/

noncomputable section
universe u

namespace PL1

theorem separableSchurLatticeRNP : SeparableSchurLatticeRNP.{u} := by
  intro F _ _ _ _ _ hS
  exact SchurLattice.hasRadonNikodymProperty_of_schur hS

theorem theoremA (𝕜 : Type u) [RCLike 𝕜] : TheoremAStatement 𝕜 :=
  theoremA_of_separableSchurLatticeRNP 𝕜 separableSchurLatticeRNP

theorem theoremAReal : TheoremARealStatement := theoremA ℝ

theorem theoremAComplexStrong : TheoremAComplexStrongStatement := theoremA ℂ

end PL1
