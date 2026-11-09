import BanachIsometric.SingularChainComplexModelIso
import BanachIsometric.RawCategoricalPrism
import BanachIsometric.RationalSingularHomologyFunctor

/-! Homotopy invariance of the actual rational chains on Mathlib's
singular simplicial set. The chain homotopy is transported through the
proved natural chain isomorphism from the literal geometric prism. -/

noncomputable section
namespace BanachIsometric

open CategoryTheory SingularPrism

variable {X Y : TopCat.{0}} {f₀ f₁ : X ⟶ Y}

def nativeSingularPrism (H : f₀.hom.Homotopy f₁.hom) :
    Homotopy (rationalSingularChainFunctor.map f₁) (rationalSingularChainFunctor.map f₀) := by
  let T := ((rawCategoricalPrism H).compRight (rawNativeSingularChainIso Y).hom).compLeft
    (rawNativeSingularChainIso X).inv
  have h₁ : (rawNativeSingularChainIso X).inv ≫
      (rawRationalChainMap f₁.hom ≫ (rawNativeSingularChainIso Y).hom) =
        rationalSingularChainFunctor.map f₁ := by
    have hn : rawRationalChainMap f₁.hom ≫ (rawNativeSingularChainIso Y).hom =
        (rawNativeSingularChainIso X).hom ≫ rationalSingularChainFunctor.map f₁ :=
      rawNativeSingularChainNatIso.hom.naturality f₁
    rw [hn]
    simp
  have h₀ : (rawNativeSingularChainIso X).inv ≫
      (rawRationalChainMap f₀.hom ≫ (rawNativeSingularChainIso Y).hom) =
        rationalSingularChainFunctor.map f₀ := by
    have hn : rawRationalChainMap f₀.hom ≫ (rawNativeSingularChainIso Y).hom =
        (rawNativeSingularChainIso X).hom ≫ rationalSingularChainFunctor.map f₀ :=
      rawNativeSingularChainNatIso.hom.naturality f₀
    rw [hn]
    simp
  exact (Homotopy.ofEq h₁.symm).trans (T.trans (Homotopy.ofEq h₀))

theorem rationalSingularHomologyMap_homotopy (H : f₀.hom.Homotopy f₁.hom) (n : ℕ) :
    (rationalSingularHomologyFunctor n).map f₀ =
      (rationalSingularHomologyFunctor n).map f₁ :=
  (nativeSingularPrism H).symm.homologyMap_eq n

end BanachIsometric
