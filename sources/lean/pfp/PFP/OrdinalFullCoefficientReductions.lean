import PFP.OrdinalInitialCoefficientPolymorphic
import PFP.OrdinalInitialQuotientPolymorphic
import PFP.OrdinalCoefficientScalarTransport
import PFP.OrdinalMatrixRepeatedFactorization
import PFP.OrdinalMatrixScalarCZero
import PFP.OrdinalRegularSquarePolymorphic

/-! Actual coefficient reductions for the full ordinal-sum theorem. The regular
matrix theorems are applied over the real and complex fields and then transported
by scalar isometries. All public endpoints allow independent scalar and ordinal
universes. Singular bases use the actual initial-ordinal isomorphisms. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000

theorem ordinalContinuous_hasUPFP_of_regular_infinite_quotient_smallScalar
    (𝕜 : Type) [RCLike 𝕜] {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) {α : Ordinal.{u}}
    (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α < c.ord * c.ord) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) := by
  letI := Posets.UniverseInitialQuotient.initialOrdinalInfiniteQuotient_index_infinite hu hlo
  have h := Posets.UniverseRegularMatrix.smallRepeatedRegularOrdinal_hasUPFP_of_scalar
    (𝕜 := 𝕜) hc hu
    (Posets.UniverseInitialQuotient.initialOrdinalInfiniteQuotient_index_small hu hhi)
    (Posets.UniverseRegularMatrix.jlmsScalarCZero_infinite_hasUPFP (𝕜 := 𝕜)
      (α / c.ord).toType)
  exact h.of_equiv
    (Posets.UniverseInitialQuotient.initialOrdinalInfiniteQuotientSumEquiv
      (𝕜 := 𝕜) hu α hlo hhi.le).symm

theorem ordinalContinuous_hasUPFP_of_regular_infinite_quotient
    (𝕜 : Type*) [RCLike 𝕜] {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) {α : Ordinal.{u}}
    (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α < c.ord * c.ord) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) :=
  ordinalContinuous_hasUPFP_of_real_complex 𝕜 α
    (ordinalContinuous_hasUPFP_of_regular_infinite_quotient_smallScalar ℝ hc hu hlo hhi)
    (ordinalContinuous_hasUPFP_of_regular_infinite_quotient_smallScalar ℂ hc hu hlo hhi)

theorem ordinalContinuous_hasUPFP_of_regular_square
    (𝕜 : Type*) [RCLike 𝕜] {c : Cardinal.{u}} (hc : c.IsRegular)
    (hu : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord * c.ord)) :=
  ordinalContinuous_hasUPFP_of_real_complex 𝕜 (c.ord * c.ord)
    (Posets.UniverseRegularMatrix.regularInitialSquare_hasUPFP (𝕜 := ℝ) hc hu)
    (Posets.UniverseRegularMatrix.regularInitialSquare_hasUPFP (𝕜 := ℂ) hc hu)

theorem ordinalContinuous_hasUPFP_of_initial_square
    (𝕜 : Type*) [RCLike 𝕜] {c : Cardinal.{u}} (hu : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ (2 : Ordinal))) := by
  by_cases hc : c.IsRegular
  · have he : c.ord ^ (2 : Ordinal) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    exact (ordinalContinuous_hasUPFP_of_regular_square 𝕜 hc hu).of_equiv
      (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).symm.toContinuousLinearEquiv
  · exact ordinalContinuous_hasUPFP_of_singular_square 𝕜 hu.le hc

theorem ordinalContinuous_hasUPFP_of_initial_principal_power
    (𝕜 : Type*) [RCLike 𝕜] {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    (g : Ordinal.{u}) (hgω : Ordinal.omega0 ≤ g) (hgP : Ordinal.Principal (· + ·) g) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ g)) := by
  have hωκ : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hc
  have hg1 : 1 < g := Ordinal.one_lt_omega0.trans_le hgω
  have hrP : Ordinal.Principal (· + ·) (c.ord * g) :=
    Ordinal.principal_add_mul_of_principal_add c.ord hg1.ne' hgP
  have hrω : Ordinal.omega0 < c.ord * g :=
    hωκ.trans_le (Ordinal.le_mul_left _ (zero_lt_one.trans hg1))
  exact (ordinalContinuous_hasUPFP_of_principal_rank 𝕜 _ hrP hrω).of_equiv
    (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜)
      (Posets.ordinal_uncountable_initial_power_rank hc g)).toContinuousLinearEquiv

theorem ordinalContinuous_hasUPFP_above_initial_square
    (𝕜 : Type*) [RCLike 𝕜] (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (α : Ordinal.{u}) (hcard : α.card ≤ c) (hsq : c.ord ^ (2 : Ordinal) ≤ α) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) := by
  obtain ⟨g, _, _, hgc, ⟨e⟩⟩ :=
    Posets.exists_ordinalSpace_canonical_power_normalForm_poly (𝕜 := 𝕜) c hc.le α hcard hsq
  apply HasUPFP.of_equiv _ e.symm
  rcases hgc with rfl | ⟨hgω, hgP⟩
  · exact ordinalContinuous_hasUPFP_of_initial_square 𝕜 hc
  · exact ordinalContinuous_hasUPFP_of_initial_principal_power 𝕜 hc g hgω hgP

end PFP
