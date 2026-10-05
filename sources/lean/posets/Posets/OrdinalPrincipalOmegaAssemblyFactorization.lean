import Posets.OrdinalPrincipalOmegaBlockModelContinuous
import Posets.OrdinalRegularOmegaAssemblyModels
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! Quantitative conversion of the concrete block identity. The block model
has norm at most 16 in both directions, so a 5/2 block factorization yields
bound 640 on the half-open ambient space. The base is any additively principal ordinal greater than ω. Selection remains an explicit input
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
local instance ordinalPrincipalOmegaFactorFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance ordinalPrincipalOmegaFactorFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance ordinalPrincipalOmegaFactorSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance ordinalPrincipalOmegaFactorSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem ordinalPrincipalOmega_factorizationWith640_of_blocks
    (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F)
    (J : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal))) →L[𝕜] E)
    (R : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal))))
    (hfactor : R.comp (A.comp J) = ContinuousLinearMap.id 𝕜 _)
    (hJ : ‖J‖ ≤ 1) (hR : ‖R‖ ≤ 5 / 2) :
    FactorsIdentityWith A (JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0))) 640 := by
  have hb : FactorsIdentityWith A
      (JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal)))) (5 / 2) := by
    refine ⟨R, J, ?_, ?_⟩
    · simpa only [ContinuousLinearMap.comp_assoc] using hfactor
    · exact (mul_le_mul hR hJ (norm_nonneg J) (by norm_num)).trans_eq (mul_one _)
  let e := ordinalPrincipalOmegaHalfOpenBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0
  have ht := hb.target_equiv e.symm
  apply ht.mono
  have hn : ‖e.symm.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖ ≤ 16 * 16 :=
    mul_le_mul (ordinalPrincipalOmegaHalfOpenBlockSumEquiv_symm_norm_le B hB hP h hh h0)
      (ordinalPrincipalOmegaHalfOpenBlockSumEquiv_norm_le B hB hP h hh h0)
      e.toContinuousLinearMap.opNorm_nonneg (by norm_num)
  change (5 / 2 : ℝ) * (‖e.symm.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖) ≤ 640
  exact (mul_le_mul_of_nonneg_left hn (by norm_num)).trans_eq (by norm_num)

theorem ordinalPrincipalOmegaHalfOpen_hasCPFP_of_block_splittings
    (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (hselect : ∀ T S : JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0)) →L[𝕜]
        JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0)),
      T + S = ContinuousLinearMap.id 𝕜 _ →
      ∃ (b : Bool) (h : ℕ → ℕ), StrictMono h ∧ 1 ≤ h 0 ∧
        ∃ (J : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal))) →L[𝕜]
            JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0)))
          (R : JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0)) →L[𝕜]
            JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal)))),
          R.comp ((if b then T else S).comp J) = ContinuousLinearMap.id 𝕜 _ ∧
            ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 5 / 2) :
    HasCPFP 𝕜 (JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0))) 640 := by
  intro T
  obtain ⟨b, h, hh, h0, J, R, hf, hJ, hR⟩ :=
    hselect T (ContinuousLinearMap.id 𝕜 _ - T) (by abel)
  have hfact := ordinalPrincipalOmega_factorizationWith640_of_blocks B hB hP h hh h0
    (if b then T else ContinuousLinearMap.id 𝕜 _ - T) J R hf hJ hR
  cases b with
  | false => exact Or.inr hfact
  | true => exact Or.inl hfact

theorem ordinalPrincipalOmegaHalfOpen_hasUPFP_of_hasCPFP640
    (B : Ordinal.{u})
    (h : HasCPFP 𝕜 (JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0))) 640) :
    HasUPFP 𝕜 (JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0))) :=
  ⟨640, by norm_num, h⟩

theorem ordinalPrincipalOmegaContinuous_hasUPFP_of_halfOpen
    (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : HasUPFP 𝕜 (JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0)))) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (B ^ Ordinal.omega0)) :=
  h.of_equiv (ordinalHalfOpenContinuousEquiv _
    (ordinalPrincipalFinitePower_infinite B hB.le _ Ordinal.one_lt_omega0.le))

end Posets


