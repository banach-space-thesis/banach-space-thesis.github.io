import BanachIsometric.FiniteNerveRationalQuotientHomology
import BanachIsometric.FiniteNerveRawSingularMap
import BanachIsometric.RawSingularHomology
import BanachIsometric.RawZeroSingularHomology

/-! The actual barycentric comparison on literal finite coordinates and on
cycles/boundaries quotients. The induced maps are constructed in every degree.
Only their image, not all singular homology, is proved finite-dimensional;
the simplicial/singular comparison isomorphism requires a separate proof. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularPrism
variable {ι : Type} [LinearOrder ι] [Fintype ι]

def finiteToRawSingularChain (K : Complex ι) (n : ℕ) :
    FiniteRationalChains K n →ₗ[ℚ] RawRationalChains K.space n :=
  (rationalToRawSingularChain K n).comp (rationalChainBasis K n).repr.symm.toLinearMap

@[simp] theorem finiteToRawSingularChain_single (K : Complex ι) (n : ℕ)
    (v : StrictOrderedSimplex K n) :
    finiteToRawSingularChain K n (Finsupp.single v 1) =
      Finsupp.single (barycentricSingularSimplex K n v) 1 := by
  simp only [finiteToRawSingularChain, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.repr_symm_single_one, rationalToRawSingularChain_basis]

theorem finiteToRawSingularChain_injective (K : Complex ι) (n : ℕ) :
    Function.Injective (finiteToRawSingularChain K n) :=
  (rationalToRawSingularChain_injective K n).comp (rationalChainBasis K n).repr.symm.injective

theorem finiteToRawSingularChain_boundary (K : Complex ι) (n : ℕ) :
    (rawBoundary (X := K.space) n).comp (finiteToRawSingularChain K (n + 1)) =
      (finiteToRawSingularChain K n).comp (finiteRationalBoundary K n) := by
  apply LinearMap.ext
  intro x
  simp only [finiteToRawSingularChain, finiteRationalBoundary, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (rationalToRawSingularChain_boundary K n)
    ((rationalChainBasis K (n + 1)).repr.symm x)

def finiteToRawSingularCycles (K : Complex ι) (n : ℕ) :
    rationalCycles K (n + 1) →ₗ[ℚ] rawCycles K.space n :=
  ((finiteToRawSingularChain K (n + 1)).comp (rationalCycles K (n + 1)).subtype).codRestrict
    (rawCycles K.space n) (by
      intro c
      change rawBoundary n (finiteToRawSingularChain K (n + 1) c.val) = 0
      have hc : finiteRationalBoundary K n c.val = 0 := c.property
      calc
        _ = finiteToRawSingularChain K n (finiteRationalBoundary K n c.val) :=
          LinearMap.congr_fun (finiteToRawSingularChain_boundary K n) c.val
        _ = 0 := by rw [hc, map_zero])

theorem finiteToRawSingularCycles_boundary (K : Complex ι) (n : ℕ)
    (x : FiniteRationalChains K (n + 2)) :
    finiteToRawSingularCycles K n (rationalBoundaryToCycles K (n + 1) x) =
      rawBoundaryCycle K.space n (finiteToRawSingularChain K (n + 2) x) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun (finiteToRawSingularChain_boundary K (n + 1)) x).symm

theorem finiteToRawSingularCycles_preserves_boundaries (K : Complex ι) (n : ℕ) :
    rationalBoundaries K (n + 1) ≤
      (rawBoundaries K.space n).comap (finiteToRawSingularCycles K n) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨finiteToRawSingularChain K (n + 2) x,
    (finiteToRawSingularCycles_boundary K n x).symm⟩

def finiteToRawPositiveHomology (K : Complex ι) (n : ℕ) :
    QuotientRationalHomology K (n + 1) →ₗ[ℚ] RawPositiveHomology K.space n :=
  (rationalBoundaries K (n + 1)).mapQ (rawBoundaries K.space n)
    (finiteToRawSingularCycles K n) (finiteToRawSingularCycles_preserves_boundaries K n)

@[simp] theorem finiteToRawPositiveHomology_mk (K : Complex ι) (n : ℕ)
    (c : rationalCycles K (n + 1)) :
    finiteToRawPositiveHomology K n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteToRawSingularCycles K n c) := rfl

instance finiteToRawPositiveHomology_range_finiteDimensional (K : Complex ι) (n : ℕ) :
    FiniteDimensional ℚ (LinearMap.range (finiteToRawPositiveHomology K n)) := by
  infer_instance

def finiteToRawZeroCycles (K : Complex ι) :
    rationalCycles K 0 →ₗ[ℚ] RawRationalChains K.space 0 :=
  (finiteToRawSingularChain K 0).comp (rationalCycles K 0).subtype

theorem finiteToRawZeroCycles_preserves_boundaries (K : Complex ι) :
    rationalBoundaries K 0 ≤
      (LinearMap.range (rawBoundary (X := K.space) 0)).comap (finiteToRawZeroCycles K) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨finiteToRawSingularChain K 1 x,
    LinearMap.congr_fun (finiteToRawSingularChain_boundary K 0) x⟩

def finiteToRawZeroHomology (K : Complex ι) :
    QuotientRationalHomology K 0 →ₗ[ℚ] RawZeroHomology K.space :=
  (rationalBoundaries K 0).mapQ (LinearMap.range (rawBoundary (X := K.space) 0))
    (finiteToRawZeroCycles K) (finiteToRawZeroCycles_preserves_boundaries K)

@[simp] theorem finiteToRawZeroHomology_mk (K : Complex ι) (c : rationalCycles K 0) :
    finiteToRawZeroHomology K (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteToRawZeroCycles K c) := rfl

instance finiteToRawZeroHomology_range_finiteDimensional (K : Complex ι) :
    FiniteDimensional ℚ (LinearMap.range (finiteToRawZeroHomology K)) := by
  infer_instance

end BanachIsometric.FiniteNerve
