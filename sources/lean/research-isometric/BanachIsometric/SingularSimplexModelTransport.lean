import BanachIsometric.NativeSimplexCoordinates
import BanachIsometric.NNRealSingularSimplexTransport
import Mathlib.AlgebraicTopology.SingularSet

/-! An actual natural equivalence between continuous simplices in real
coordinates and Mathlib's singular simplicial set, including its universe
lifts. No homological comparison theorem is assumed. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open CategoryTheory Simplicial Opposite
open scoped Topology

def rawNativeSingularEquiv (X : TopCat.{0}) (n : ℕ) :
    RawSingularSimplex X n ≃ (TopCat.toSSet.obj X).obj (op ⦋n⦌) :=
  (realNNRealSingularEquiv X n).trans (TopCat.toSSetObjEquiv X (op ⦋n⦌)).symm

theorem nativeSingularEquiv_precomp (X : TopCat.{0}) {a b : ℕ}
    (f : ⦋a⦌ ⟶ ⦋b⦌) (simplex : (TopCat.toSSet.obj X).obj (op ⦋b⦌)) :
    TopCat.toSSetObjEquiv X (op ⦋a⦌) ((TopCat.toSSet.obj X).map f.op simplex) =
      (TopCat.toSSetObjEquiv X (op ⦋b⦌) simplex).comp
        ⟨SimplexCategory.toTopMap f, SimplexCategory.continuous_toTopMap f⟩ := by
  apply ContinuousMap.ext
  intro w
  rfl

theorem rawNativeSingularEquiv_precomp (X : TopCat.{0}) {a b : ℕ}
    (f : ⦋a⦌ ⟶ ⦋b⦌) (simplex : RawSingularSimplex X b) :
    rawNativeSingularEquiv X a (simplex.comp (simplexMap f)) =
      (TopCat.toSSet.obj X).map f.op (rawNativeSingularEquiv X b simplex) := by
  apply (TopCat.toSSetObjEquiv X (op ⦋a⦌)).injective
  rw [nativeSingularEquiv_precomp]
  simp only [rawNativeSingularEquiv, Equiv.trans_apply]
  rw [realNNRealSingularEquiv_precomp]
  apply ContinuousMap.ext
  intro w
  exact congrArg (realNNRealSingularEquiv X b simplex)
    (nnrealNativeSimplex_natural f w)

theorem rawNativeSingularEquiv_face (X : TopCat.{0}) (n : ℕ)
    (i : Fin (n + 2)) (simplex : RawSingularSimplex X (n + 1)) :
    rawNativeSingularEquiv X n (simplex.comp (face i)) =
      (TopCat.toSSet.obj X).δ i (rawNativeSingularEquiv X (n + 1) simplex) :=
  rawNativeSingularEquiv_precomp X (SimplexCategory.δ i) simplex

theorem rawNativeSingularEquiv_postcomp {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (simplex : RawSingularSimplex X n) :
    rawNativeSingularEquiv Y n (f.hom.comp simplex) =
      (TopCat.toSSet.map f).app (op ⦋n⦌) (rawNativeSingularEquiv X n simplex) := by
  apply (TopCat.toSSetObjEquiv Y (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro w
  rfl

end BanachIsometric.SingularPrism
