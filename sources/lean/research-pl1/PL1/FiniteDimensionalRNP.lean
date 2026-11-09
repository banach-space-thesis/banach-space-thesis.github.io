import PL1.RNPBridge
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

/-! # Finite-dimensional spaces satisfy the full reviewed RNP -/

noncomputable section
universe u v w
open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace PL1.RNPBridge

/-- Scalar Radon–Nikodym is exactly the reviewed RNP in dimension one. -/
theorem hasRadonNikodymProperty_real : HasRadonNikodymProperty.{0, w} ℝ := by
  intro Ω mΩ
  let := mΩ
  intro μ hμ ν hν hAC
  let : IsFiniteMeasure μ := ⟨hμ⟩
  have ha : ν ≪ᵥ μ.toENNRealVectorMeasure := by
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro A hA hzero
    rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hzero
    exact hAC A hA hzero
  refine ⟨SignedMeasure.rnDeriv ν μ, SignedMeasure.integrable_rnDeriv ν μ, ?_⟩
  intro A hA
  have h := congrArg (fun s : SignedMeasure Ω => s A)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq ν μ ha)
  rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv ν μ) hA] at h
  exact h.symm

/-- Finite products of real lines have densities coordinate by coordinate. -/
theorem hasRadonNikodymProperty_real_pi (ι : Type v) [Fintype ι] :
    HasRadonNikodymProperty.{v, w} (ι → ℝ) := by
  classical
  intro Ω mΩ
  let := mΩ
  intro μ hμ ν hν hAC
  let s (i : ι) : VectorMeasure Ω ℝ := mapVectorMeasure (ContinuousLinearMap.proj i) ν
  have hsAC (i : ι) : ∀ A : Set Ω, MeasurableSet A → μ A = 0 → s i A = 0 := by
    intro A hA hz
    change (ν A) i = 0
    rw [hAC A hA hz]
    rfl
  have hsvar (i : ι) : (s i).variation univ < ∞ := by
    change (mapVectorMeasure (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) ν).variation univ < ∞
    exact mapVectorMeasure_finite_variation _ ν hν
  have hs (i : ι) : ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ A : Set Ω, MeasurableSet A → s i A = ∫ x in A, g x ∂μ :=
    hasRadonNikodymProperty_real Ω mΩ μ hμ (s i) (hsvar i) (hsAC i)
  choose g hg hrepr using hs
  refine ⟨fun x i => g i x, Integrable.of_eval hg, ?_⟩
  intro A hA
  funext i
  rw [eval_integral (fun j => (hg j).integrableOn)]
  exact hrepr i A hA

/-- Every finite-dimensional real normed space has the full vector-measure RNP. -/
theorem hasRadonNikodymProperty_of_finiteDimensional
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    HasRadonNikodymProperty.{u, w} E := by
  let e := (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  exact hasRadonNikodymProperty_of_equiv e.symm
    (hasRadonNikodymProperty_real_pi (Fin (Module.finrank ℝ E)))

/-- Failure of the reviewed RNP witnesses infinite real dimension. -/
theorem not_finiteDimensional_of_not_RNP
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬ HasRadonNikodymProperty.{u, w} E) : ¬ FiniteDimensional ℝ E := by
  intro h
  let := h
  exact hE (hasRadonNikodymProperty_of_finiteDimensional E)

/-- Finite dimension over either scalar field implies real RNP for the explicit
underlying-real space used by the reviewed statements. -/
theorem underlyingReal_hasRNP_of_finiteDimensional
    (𝕜 : Type*) [RCLike 𝕜] (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] :
    @HasRadonNikodymProperty.{u, w} (UnderlyingReal 𝕜 E)
      (inferInstanceAs (NormedAddCommGroup E)) (NormedSpace.restrictScalars ℝ 𝕜 E) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ 𝕜 E
  exact hasRadonNikodymProperty_of_finiteDimensional E

/-- Failure of underlying-real RNP implies infinite dimension over ℝ or ℂ. -/
theorem not_finiteDimensional_scalar_of_not_RNP
    (𝕜 : Type*) [RCLike 𝕜] (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hE : ¬ @HasRadonNikodymProperty.{u, w} (UnderlyingReal 𝕜 E)
      (inferInstanceAs (NormedAddCommGroup E)) (NormedSpace.restrictScalars ℝ 𝕜 E)) :
    ¬ FiniteDimensional 𝕜 E := by
  intro h
  let := h
  exact hE (underlyingReal_hasRNP_of_finiteDimensional 𝕜 E)

end PL1.RNPBridge




