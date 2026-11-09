import BanachIsometric.RealNNRealSimplex
import BanachIsometric.RawSingularChains

/-! Actual singular-simplex and free rational-chain coordinate equivalences
between the real and nonnegative-real simplex models, natural in both the
vertex map and the target continuous map. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def realNNRealSingularEquiv (X : Type*) [TopologicalSpace X] (n : ℕ) :
    RawSingularSimplex X n ≃ C(NNRealSimplex n, X) where
  toFun simplex := simplex.comp ⟨(realNNRealSimplex n).symm, (realNNRealSimplex n).symm.continuous⟩
  invFun simplex := simplex.comp ⟨realNNRealSimplex n, (realNNRealSimplex n).continuous⟩
  left_inv simplex := by
    apply ContinuousMap.ext
    intro w
    exact congrArg simplex ((realNNRealSimplex n).symm_apply_apply w)
  right_inv simplex := by
    apply ContinuousMap.ext
    intro w
    exact congrArg simplex ((realNNRealSimplex n).apply_symm_apply w)

theorem realNNRealSimplex_symm_natural {a b : ℕ}
    (f : Fin (a + 1) → Fin (b + 1)) (w : NNRealSimplex a) :
    stdSimplex.map f ((realNNRealSimplex a).symm w) =
      (realNNRealSimplex b).symm (nnrealSimplexMap f w) := by
  apply (realNNRealSimplex b).injective
  rw [(realNNRealSimplex b).apply_symm_apply]
  simpa only [(realNNRealSimplex a).apply_symm_apply] using
    realNNRealSimplex_natural f ((realNNRealSimplex a).symm w)

theorem realNNRealSingularEquiv_precomp {a b : ℕ}
    (f : Fin (a + 1) → Fin (b + 1)) (simplex : RawSingularSimplex X b) :
    realNNRealSingularEquiv X a (simplex.comp (simplexMap f)) =
      (realNNRealSingularEquiv X b simplex).comp (nnrealSimplexMap f) := by
  apply ContinuousMap.ext
  intro w
  exact congrArg simplex (realNNRealSimplex_symm_natural f w)

theorem realNNRealSingularEquiv_postcomp (f : C(X, Y)) (n : ℕ)
    (simplex : RawSingularSimplex X n) :
    realNNRealSingularEquiv Y n (f.comp simplex) =
      f.comp (realNNRealSingularEquiv X n simplex) := rfl

def realNNRealSingularChainEquiv (X : Type*) [TopologicalSpace X] (n : ℕ) :
    RawRationalChains X n ≃ₗ[ℚ] (C(NNRealSimplex n, X) →₀ ℚ) :=
  Finsupp.mapDomain.linearEquiv ℚ ℚ (realNNRealSingularEquiv X n)

theorem realNNRealSingularChainEquiv_single (n : ℕ)
    (simplex : RawSingularSimplex X n) (a : ℚ) :
    realNNRealSingularChainEquiv X n (Finsupp.single simplex a) =
      Finsupp.single (realNNRealSingularEquiv X n simplex) a := by
  simp only [realNNRealSingularChainEquiv, Finsupp.mapDomain.coe_linearEquiv,
    Finsupp.mapDomain_single]

end BanachIsometric.SingularPrism
