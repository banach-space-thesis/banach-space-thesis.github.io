import BanachIsometric.SingularSimplexModelTransport
import BanachIsometric.RationalSingularChains

/-! An actual linear equivalence between the concrete real-coordinate
singular chains and the free rational chains on Mathlib's singular set.
Both differentials and continuous-map actions commute with it. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open CategoryTheory Simplicial Opposite

def rawNativeSingularChainEquiv (X : TopCat.{0}) (n : ℕ) :
    RawRationalChains X n ≃ₗ[ℚ] RationalSingularChains X n :=
  Finsupp.mapDomain.linearEquiv ℚ ℚ (rawNativeSingularEquiv X n)

theorem rawNativeSingularChainEquiv_single (X : TopCat.{0}) (n : ℕ)
    (simplex : RawSingularSimplex X n) (a : ℚ) :
    rawNativeSingularChainEquiv X n (Finsupp.single simplex a) =
      Finsupp.single (rawNativeSingularEquiv X n simplex) a := by
  simp only [rawNativeSingularChainEquiv, Finsupp.mapDomain.coe_linearEquiv,
    Finsupp.mapDomain_single]

theorem rawNativeSingularChainEquiv_boundary (X : TopCat.{0}) (n : ℕ) :
    (rationalSingularBoundary X n).comp (rawNativeSingularChainEquiv X (n + 1)).toLinearMap =
      (rawNativeSingularChainEquiv X n).toLinearMap.comp (rawBoundary n) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have hsingle : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    rawNativeSingularChainEquiv_single, rationalSingularBoundary_single,
    rawBoundary_single, map_sum, map_zsmul, rawNativeSingularEquiv_face]

theorem rawNativeSingularChainEquiv_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    ((rationalSingularChainFunctor.map f).f n).hom.comp
      (rawNativeSingularChainEquiv X n).toLinearMap =
        (rawNativeSingularChainEquiv Y n).toLinearMap.comp (rawChainMap f.hom n) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have hsingle : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  change ((rationalSingularChainFunctor.map f).f n)
      (rawNativeSingularChainEquiv X n (Finsupp.single simplex 1)) =
    rawNativeSingularChainEquiv Y n (rawChainMap f.hom n (Finsupp.single simplex 1))
  rw [rawNativeSingularChainEquiv_single, rationalSingularChainFunctor_map_single]
  simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [rawNativeSingularChainEquiv_single, rawNativeSingularEquiv_postcomp]

end BanachIsometric.SingularPrism
