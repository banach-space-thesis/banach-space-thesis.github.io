import BanachIsometric.FiniteNerveRationalCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Actual cycles modulo actual boundaries of the finite ordered-face chain
complex, including degree zero. The dual cochain boundary is precomposition
with the proved chain boundary. Both quotient homology and quotient cohomology
are finite-dimensional rational vector spaces and vanish above the vertex
bound. No realization-to-singular comparison is asserted here. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def rationalOutgoingBoundary (K : Complex ι) :
    (n : ℕ) → FiniteRationalChains K n →ₗ[ℚ] FiniteRationalChains K (n - 1)
  | 0 => 0
  | n + 1 => finiteRationalBoundary K n

theorem rationalOutgoingBoundary_comp (K : Complex ι) (n : ℕ) :
    (rationalOutgoingBoundary K n).comp (finiteRationalBoundary K n) = 0 := by
  cases n with
  | zero => rfl
  | succ n => exact finiteRationalBoundary_squared K n

def rationalCycles (K : Complex ι) (n : ℕ) : Submodule ℚ (FiniteRationalChains K n) :=
  LinearMap.ker (rationalOutgoingBoundary K n)

def rationalBoundaryToCycles (K : Complex ι) (n : ℕ) :
    FiniteRationalChains K (n + 1) →ₗ[ℚ] rationalCycles K n :=
  (finiteRationalBoundary K n).codRestrict _ fun x =>
    LinearMap.congr_fun (rationalOutgoingBoundary_comp K n) x

def rationalBoundaries (K : Complex ι) (n : ℕ) : Submodule ℚ (rationalCycles K n) :=
  LinearMap.range (rationalBoundaryToCycles K n)

abbrev QuotientRationalHomology (K : Complex ι) (n : ℕ) :=
  (rationalCycles K n) ⧸ (rationalBoundaries K n)

instance quotientRationalHomology_finiteDimensional (K : Complex ι) (n : ℕ) :
    FiniteDimensional ℚ (QuotientRationalHomology K n) := by
  infer_instance

theorem subsingleton_quotientRationalHomology_of_card_le (K : Complex ι) (n : ℕ)
    (hn : Fintype.card ι ≤ n) : Subsingleton (QuotientRationalHomology K n) := by
  letI : Subsingleton (FiniteRationalChains K n) := subsingleton_finiteRationalChains_of_card_le K n hn
  apply (Submodule.Quotient.subsingleton_iff _).mpr
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx]
  exact (rationalBoundaries K n).zero_mem

abbrev QuotientRationalCochains (K : Complex ι) (n : ℕ) := FiniteRationalChains K n →ₗ[ℚ] ℚ

def quotientRationalCoboundary (K : Complex ι) (n : ℕ) :
    QuotientRationalCochains K n →ₗ[ℚ] QuotientRationalCochains K (n + 1) where
  toFun ℓ := ℓ.comp (finiteRationalBoundary K n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quotientRationalCoboundary_squared (K : Complex ι) (n : ℕ) :
    (quotientRationalCoboundary K (n + 1)).comp (quotientRationalCoboundary K n) = 0 := by
  apply LinearMap.ext
  intro ℓ
  apply LinearMap.ext
  intro x
  change ℓ (finiteRationalBoundary K n (finiteRationalBoundary K (n + 1) x)) = 0
  have hx := LinearMap.congr_fun (finiteRationalBoundary_squared K n) x
  change finiteRationalBoundary K n (finiteRationalBoundary K (n + 1) x) = 0 at hx
  rw [hx, map_zero]

def rationalIncomingCoboundary (K : Complex ι) :
    (n : ℕ) → QuotientRationalCochains K (n - 1) →ₗ[ℚ] QuotientRationalCochains K n
  | 0 => 0
  | n + 1 => quotientRationalCoboundary K n

theorem rationalIncomingCoboundary_comp (K : Complex ι) (n : ℕ) :
    (quotientRationalCoboundary K n).comp (rationalIncomingCoboundary K n) = 0 := by
  cases n with
  | zero => simp [rationalIncomingCoboundary]
  | succ n => exact quotientRationalCoboundary_squared K n

def rationalCocycles (K : Complex ι) (n : ℕ) : Submodule ℚ (QuotientRationalCochains K n) :=
  LinearMap.ker (quotientRationalCoboundary K n)

def rationalCoboundaryToCocycles (K : Complex ι) (n : ℕ) :
    QuotientRationalCochains K (n - 1) →ₗ[ℚ] rationalCocycles K n :=
  (rationalIncomingCoboundary K n).codRestrict _ fun x =>
    LinearMap.congr_fun (rationalIncomingCoboundary_comp K n) x

def rationalCoboundaries (K : Complex ι) (n : ℕ) : Submodule ℚ (rationalCocycles K n) :=
  LinearMap.range (rationalCoboundaryToCocycles K n)

abbrev QuotientRationalCohomology (K : Complex ι) (n : ℕ) :=
  rationalCocycles K n ⧸ rationalCoboundaries K n

instance quotientRationalCohomology_finiteDimensional (K : Complex ι) (n : ℕ) :
    FiniteDimensional ℚ (QuotientRationalCohomology K n) := by
  infer_instance

theorem subsingleton_quotientRationalCohomology_of_card_le (K : Complex ι) (n : ℕ)
    (hn : Fintype.card ι ≤ n) : Subsingleton (QuotientRationalCohomology K n) := by
  letI : Subsingleton (FiniteRationalChains K n) := subsingleton_finiteRationalChains_of_card_le K n hn
  apply (Submodule.Quotient.subsingleton_iff _).mpr
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx]
  exact (rationalCoboundaries K n).zero_mem

end BanachIsometric.FiniteNerve

