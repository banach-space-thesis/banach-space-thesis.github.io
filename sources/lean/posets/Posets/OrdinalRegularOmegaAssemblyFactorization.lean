import Posets.OrdinalRegularOmegaAssemblyModels
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! Quantitative conversion of the concrete block identity. The block model
has norm at most 16 in both directions, so a 5/2 block factorization yields
bound 640 on the half-open ambient space. Selection remains an explicit input
in the final all-operator assembly lemmas. -/
noncomputable section
open Set
namespace Posets
open ThesisCommon
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
local instance ordinalOmegaFactorFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance ordinalOmegaFactorFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance ordinalOmegaFactorSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance ordinalOmegaFactorSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem ordinalOmega_factorizationWith640_of_blocks
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F)
    (J : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal))) →L[𝕜] E)
    (R : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal))))
    (hfactor : R.comp (A.comp J) = ContinuousLinearMap.id 𝕜 _)
    (hJ : ‖J‖ ≤ 1) (hR : ‖R‖ ≤ 5 / 2) :
    FactorsIdentityWith A (JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))) 640 := by
  have hb : FactorsIdentityWith A
      (JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal)))) (5 / 2) := by
    refine ⟨R, J, ?_, ?_⟩
    · simpa only [ContinuousLinearMap.comp_assoc] using hfactor
    · exact (mul_le_mul hR hJ (norm_nonneg J) (by norm_num)).trans_eq (mul_one _)
  let e := ordinalOmegaHalfOpenBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0
  have ht := hb.target_equiv e.symm
  apply ht.mono
  have hn : ‖e.symm.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖ ≤ 16 * 16 :=
    mul_le_mul (ordinalOmegaHalfOpenBlockSumEquiv_symm_norm_le c hc h hh h0)
      (ordinalOmegaHalfOpenBlockSumEquiv_norm_le c hc h hh h0)
      e.toContinuousLinearMap.opNorm_nonneg (by norm_num)
  change (5 / 2 : ℝ) * (‖e.symm.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖) ≤ 640
  exact (mul_le_mul_of_nonneg_left hn (by norm_num)).trans_eq (by norm_num)

theorem ordinalOmegaHalfOpen_hasCPFP_of_block_splittings
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (hselect : ∀ T S : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
        JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)),
      T + S = ContinuousLinearMap.id 𝕜 _ →
      ∃ (b : Bool) (h : ℕ → ℕ), StrictMono h ∧ 2 ≤ h 0 ∧
        ∃ (J : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal))) →L[𝕜]
            JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)))
          (R : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
            JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal)))),
          R.comp ((if b then T else S).comp J) = ContinuousLinearMap.id 𝕜 _ ∧
            ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 5 / 2) :
    HasCPFP 𝕜 (JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))) 640 := by
  intro T
  obtain ⟨b, h, hh, h0, J, R, hf, hJ, hR⟩ :=
    hselect T (ContinuousLinearMap.id 𝕜 _ - T) (by abel)
  have hfact := ordinalOmega_factorizationWith640_of_blocks c hc h hh h0
    (if b then T else ContinuousLinearMap.id 𝕜 _ - T) J R hf hJ hR
  cases b with
  | false => exact Or.inr hfact
  | true => exact Or.inl hfact

theorem ordinalOmegaHalfOpen_hasUPFP_of_hasCPFP640
    (c : Cardinal.{u})
    (h : HasCPFP 𝕜 (JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))) 640) :
    HasUPFP 𝕜 (JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))) :=
  ⟨640, by norm_num, h⟩

theorem ordinalOmegaContinuous_hasUPFP_of_halfOpen
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : HasUPFP 𝕜 (JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)))) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (c.ord ^ Ordinal.omega0)) :=
  h.of_equiv (ordinalHalfOpenContinuousEquiv _
    (JLMS.ordinalInitialPower_infinite c hc _ Ordinal.one_lt_omega0.le))

end Posets

