import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import BanachIsometric.RationalFreeModule
import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Concrete rational singular chains

The actual simplices are Mathlib's continuous topological simplices. The
free rational module is implemented by finitely supported rational functions,
and its actual alternating face maps form the chain complex. This is the
concrete model shared by the prism and finite-simplex comparison maps.

Mathlib's separate `singularChainComplexFunctor` uses a chosen categorical
coproduct. No identification with that implementation is assumed here.
-/

noncomputable section
namespace BanachIsometric

open CategoryTheory Simplicial Opposite AlgebraicTopology

abbrev RationalSingularSimplex (X : TopCat.{0}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (op ⦋n⦌)

abbrev RationalSingularChains (X : TopCat.{0}) (n : ℕ) := RationalSingularSimplex X n →₀ ℚ

def rationalSingularSimplicialFunctor : TopCat.{0} ⥤ SimplicialObject (ModuleCat ℚ) :=
  TopCat.toSSet ⋙ (SimplicialObject.whiskering (Type) (ModuleCat ℚ)).obj rationalFreeModule

def rationalSingularChainFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
  rationalSingularSimplicialFunctor ⋙ alternatingFaceMapComplex (ModuleCat ℚ)

abbrev rationalSingularChainComplex (X : TopCat.{0}) := rationalSingularChainFunctor.obj X

def rationalSingularBoundary (X : TopCat.{0}) (n : ℕ) :
    RationalSingularChains X (n + 1) →ₗ[ℚ] RationalSingularChains X n :=
  (AlternatingFaceMapComplex.objD (rationalSingularSimplicialFunctor.obj X) n).hom

theorem rationalSingularBoundary_squared (X : TopCat.{0}) (n : ℕ) :
    (rationalSingularBoundary X n).comp (rationalSingularBoundary X (n + 1)) = 0 :=
  ModuleCat.hom_ext_iff.mp
    (AlternatingFaceMapComplex.d_squared (rationalSingularSimplicialFunctor.obj X) n)

theorem rationalSingularBoundary_single (X : TopCat.{0}) (n : ℕ)
    (σ : RationalSingularSimplex X (n + 1)) :
    rationalSingularBoundary X n (Finsupp.single σ 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.single ((TopCat.toSSet.obj X).δ i σ) 1 := by
  have he : rationalSingularBoundary X n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.lmapDomain ℚ ℚ ((TopCat.toSSet.obj X).δ i) := by
    simp only [rationalSingularBoundary, AlternatingFaceMapComplex.objD,
      ModuleCat.hom_sum, ModuleCat.hom_smul]
    rfl
  rw [he]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact rationalFreeModule_map_single ((TopCat.toSSet.obj X).δ i) σ 1

theorem rationalSingularChainFunctor_map_single {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (σ : RationalSingularSimplex X n) :
    ((rationalSingularChainFunctor.map f).f n) (Finsupp.single σ 1) =
      Finsupp.single ((TopCat.toSSet.map f).app (op ⦋n⦌) σ) 1 :=
  rationalFreeModule_map_single ((TopCat.toSSet.map f).app (op ⦋n⦌)) σ 1

end BanachIsometric
