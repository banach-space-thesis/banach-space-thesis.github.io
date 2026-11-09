import BanachIsometric.FiniteNerveRationalBoundary

/-! Literal finite Finsupp coordinates for the proved ordered-face chain
complex. Every boundary is transported through the actual finite face basis.
This also makes its concrete cycle quotients independent of subtype instance
choices. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]

abbrev FiniteRationalChains (K : Complex ι) (n : ℕ) := StrictOrderedSimplex K n →₀ ℚ

def finiteRationalBoundary (K : Complex ι) (n : ℕ) :
    FiniteRationalChains K (n + 1) →ₗ[ℚ] FiniteRationalChains K n :=
  (rationalChainBasis K n).repr.toLinearMap.comp
    ((rationalBoundary K n).comp (rationalChainBasis K (n + 1)).repr.symm.toLinearMap)

theorem finiteRationalBoundary_squared (K : Complex ι) (n : ℕ) :
    (finiteRationalBoundary K n).comp (finiteRationalBoundary K (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [finiteRationalBoundary, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  have hx := LinearMap.congr_fun (rationalBoundary_squared K n)
    ((rationalChainBasis K (n + 2)).repr.symm x)
  change rationalBoundary K n (rationalBoundary K (n + 1) _) = 0 at hx
  rw [hx, map_zero]
  rfl

theorem finiteRationalBoundary_single (K : Complex ι) (n : ℕ)
    (v : StrictOrderedSimplex K (n + 1)) :
    finiteRationalBoundary K n (Finsupp.single v 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (strictOrderedFace K i v) 1 := by
  simp only [finiteRationalBoundary, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.repr_symm_single_one, rationalBoundary_basis, map_sum, map_zsmul,
    Module.Basis.repr_self]

theorem finiteRationalBoundary_repr (K : Complex ι) (n : ℕ) (x : RationalChains K (n + 1)) :
    finiteRationalBoundary K n ((rationalChainBasis K (n + 1)).repr x) =
      (rationalChainBasis K n).repr (rationalBoundary K n x) := by
  simp [finiteRationalBoundary]

instance (K : Complex ι) (n : ℕ) : FiniteDimensional ℚ (FiniteRationalChains K n) := by
  infer_instance

theorem subsingleton_finiteRationalChains_of_card_le (K : Complex ι) (n : ℕ)
    (hn : Fintype.card ι ≤ n) : Subsingleton (FiniteRationalChains K n) := by
  letI : IsEmpty (StrictOrderedSimplex K n) := isEmpty_strictOrderedSimplex K n hn
  infer_instance

def finiteRationalChainComplex (K : Complex ι) : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℚ (FiniteRationalChains K n))
    (fun n => ModuleCat.ofHom (finiteRationalBoundary K n))
    (fun n => ModuleCat.hom_ext (finiteRationalBoundary_squared K n))

end BanachIsometric.FiniteNerve
