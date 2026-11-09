import BanachIsometric.RealNNRealSimplex
import Mathlib.AlgebraicTopology.TopologicalSimplex

/-! The nonnegative coordinate simplex is the literal topological-simplex
model used by Mathlib. Its maps agree with the actual finite vertex maps,
including every face and degeneracy map. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open CategoryTheory Simplicial
open scoped NNReal

def nnrealNativeSimplex (n : ℕ) : NNRealSimplex n ≃ₜ ⦋n⦌.toTopObj :=
  Homeomorph.refl _

theorem nnrealNativeSimplex_natural {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌)
    (w : NNRealSimplex a) :
    nnrealNativeSimplex b (nnrealSimplexMap f w) =
      SimplexCategory.toTopMap f (nnrealNativeSimplex a w) := by
  apply Subtype.ext
  funext i
  exact nnrealSimplexMap_apply f w i

theorem realNativeSimplex_natural {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌)
    (w : Simplex a) :
    nnrealNativeSimplex b (realNNRealSimplex b (stdSimplex.map f w)) =
      SimplexCategory.toTopMap f (nnrealNativeSimplex a (realNNRealSimplex a w)) := by
  rw [realNNRealSimplex_natural]
  exact nnrealNativeSimplex_natural f _

end BanachIsometric.SingularPrism
