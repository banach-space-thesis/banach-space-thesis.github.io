import BanachIsometric.FiniteNerveRationalCoordinates
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Actual bounded rational homology and cohomology of a finite face complex

The chain boundary was constructed from actual ordered-face deletion and its
square was proved zero. Homology here is Mathlib's homology of that actual
chain complex, explicitly identified with cycles modulo actual boundaries.
Dualizing gives an actual cochain complex. Every resulting group is a
finite-dimensional rational vector space and vanishes above the vertex bound.

No claim identifies these groups with singular homology of the geometric
realization, nor with homology of a dominated topological space.
-/

noncomputable section
namespace BanachIsometric.FiniteNerve

open CategoryTheory

theorem finiteDimensional_shortComplex_homology (S : ShortComplex (ModuleCat ℚ))
    [FiniteDimensional ℚ S.X₂] : FiniteDimensional ℚ S.homology := by
  letI : FiniteDimensional ℚ S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional ℚ (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact FiniteDimensional.of_injective S.moduleCatHomologyIso.toLinearEquiv.toLinearMap
    S.moduleCatHomologyIso.toLinearEquiv.injective

theorem subsingleton_shortComplex_homology (S : ShortComplex (ModuleCat ℚ))
    [Subsingleton S.X₂] : Subsingleton S.homology := by
  letI : Subsingleton S.moduleCatLeftHomologyData.H := by
    change Subsingleton (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    apply (Submodule.Quotient.subsingleton_iff _).mpr
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact (LinearMap.range S.moduleCatToCycles).zero_mem
  exact S.moduleCatHomologyIso.toLinearEquiv.injective.subsingleton

variable {ι : Type} [LinearOrder ι] [Fintype ι]

abbrev RationalHomology (K : Complex ι) (n : ℕ) := (finiteRationalChainComplex K).homology n

def rationalHomology_cyclesQuotient_equiv (K : Complex ι) (n : ℕ) :
    RationalHomology K n ≃ₗ[ℚ]
      (LinearMap.ker ((finiteRationalChainComplex K).sc n).g.hom ⧸
        LinearMap.range ((finiteRationalChainComplex K).sc n).moduleCatToCycles) :=
  ((finiteRationalChainComplex K).sc n).moduleCatHomologyIso.toLinearEquiv

instance rationalHomology_finiteDimensional (K : Complex ι) (n : ℕ) :
    FiniteDimensional ℚ (RationalHomology K n) := by
  letI : FiniteDimensional ℚ ((finiteRationalChainComplex K).sc n).X₂ := by
    change FiniteDimensional ℚ (FiniteRationalChains K n)
    infer_instance
  exact finiteDimensional_shortComplex_homology _

theorem subsingleton_rationalHomology_of_card_le (K : Complex ι) (n : ℕ)
    (hn : Fintype.card ι ≤ n) : Subsingleton (RationalHomology K n) := by
  letI : Subsingleton ((finiteRationalChainComplex K).sc n).X₂ :=
    subsingleton_finiteRationalChains_of_card_le K n hn
  exact subsingleton_shortComplex_homology _

abbrev RationalCochains (K : Complex ι) (n : ℕ) := FiniteRationalChains K n →ₗ[ℚ] ℚ

def rationalCoboundary (K : Complex ι) (n : ℕ) :
    RationalCochains K n →ₗ[ℚ] RationalCochains K (n + 1) where
  toFun ℓ := ℓ.comp (finiteRationalBoundary K n)
  map_add' ℓ₁ ℓ₂ := by ext x; rfl
  map_smul' c ℓ := by ext x; rfl

theorem rationalCoboundary_squared (K : Complex ι) (n : ℕ) :
    (rationalCoboundary K (n + 1)).comp (rationalCoboundary K n) = 0 := by
  apply LinearMap.ext
  intro ℓ
  apply LinearMap.ext
  intro x
  change ℓ (finiteRationalBoundary K n (finiteRationalBoundary K (n + 1) x)) = 0
  have hx := LinearMap.congr_fun (finiteRationalBoundary_squared K n) x
  change finiteRationalBoundary K n (finiteRationalBoundary K (n + 1) x) = 0 at hx
  rw [hx, map_zero]

def rationalCochainComplex (K : Complex ι) : CochainComplex (ModuleCat ℚ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℚ (RationalCochains K n))
    (fun n => ModuleCat.ofHom (rationalCoboundary K n))
    (fun n => ModuleCat.hom_ext (rationalCoboundary_squared K n))

abbrev RationalCohomology (K : Complex ι) (n : ℕ) := (rationalCochainComplex K).homology n

instance rationalCohomology_finiteDimensional (K : Complex ι) (n : ℕ) :
    FiniteDimensional ℚ (RationalCohomology K n) := by
  letI : FiniteDimensional ℚ ((rationalCochainComplex K).sc n).X₂ := by
    change FiniteDimensional ℚ (RationalCochains K n)
    infer_instance
  exact finiteDimensional_shortComplex_homology _

theorem subsingleton_rationalCohomology_of_card_le (K : Complex ι) (n : ℕ)
    (hn : Fintype.card ι ≤ n) : Subsingleton (RationalCohomology K n) := by
  letI : Subsingleton (FiniteRationalChains K n) := subsingleton_finiteRationalChains_of_card_le K n hn
  letI : Subsingleton ((rationalCochainComplex K).sc n).X₂ := by
    change Subsingleton (RationalCochains K n)
    infer_instance
  exact subsingleton_shortComplex_homology _

end BanachIsometric.FiniteNerve

