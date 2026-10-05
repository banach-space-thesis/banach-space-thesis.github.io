import Posets.OrdinalVariableUnitSelectedFactorization
import Posets.OrdinalVariableUnitChoice
import Posets.OrdinalPrincipalCofinalBlockModel
import Posets.OrdinalHigherLimitRankParameters
import Posets.OrdinalRankUnitOmegaPreservation

/-! Unconditional preservation at every additive-principal rank of
countable cofinality. The selected target blocks are actual cofinal compact
ordinal intervals; their model bounds are independent of the operators. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000

local instance variablePreservationWeakOrdinal : WeaklyLocallyCompactSpace Ordinal.{u} where
  exists_compact_mem_nhds x := ⟨Iic x, ordinalClosedCore_interval_compact x,
    (ordinal_isClopen_Iic x).isOpen.mem_nhds (show x ≤ x from le_rfl)⟩
local instance variablePreservationLocallyCompact (Γ : Ordinal.{u}) :
    LocallyCompactSpace (Iio Γ) := isOpen_Iio.locallyCompactSpace
local instance variablePreservationFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance variablePreservationFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance variablePreservationSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance variablePreservationSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem ordinalCofinalBlocks_factorizationWith160
    {Γ : Ordinal.{u}} (P : OrdinalPrincipalCofinalSequence Γ)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F)
    (J : JLMS.CZeroSum 𝕜 (fun i : ℕ => JLMS.OrdinalC 𝕜 (P.endpoint i)) →L[𝕜] E)
    (R : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun i : ℕ => JLMS.OrdinalC 𝕜 (P.endpoint i)))
    (hf : R.comp (A.comp J) = ContinuousLinearMap.id 𝕜 _)
    (hJ : ‖J‖ ≤ 1) (hR : ‖R‖ ≤ 5 / 2) :
    FactorsIdentityWith A (JLMS.CZero 𝕜 (Iio Γ)) 160 := by
  have hb : FactorsIdentityWith A
      (JLMS.CZeroSum 𝕜 (fun i : ℕ => JLMS.OrdinalC 𝕜 (P.endpoint i))) (5 / 2) := by
    refine ⟨R, J, ?_, ?_⟩
    · simpa only [ContinuousLinearMap.comp_assoc] using hf
    · exact (mul_le_mul hR hJ (norm_nonneg J) (by norm_num)).trans_eq (mul_one _)
  have ht := hb.target_equiv (P.halfOpenBlockSumEquiv (𝕜 := 𝕜)).symm
  apply ht.mono
  have hn : ‖(P.halfOpenBlockSumEquiv (𝕜 := 𝕜)).symm.toContinuousLinearMap‖ *
      ‖(P.halfOpenBlockSumEquiv (𝕜 := 𝕜)).toContinuousLinearMap‖ ≤ 8 * 8 :=
    mul_le_mul P.halfOpenBlockSumEquiv_symm_norm_le P.halfOpenBlockSumEquiv_norm_le
      (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 5 / 2)).trans_eq (by norm_num)

namespace OrdinalVariableUnitColouredCores

def cofinalBlockSequence {γ : Ordinal.{u}} {N : ℕ} {P : OrdinalVariableUnitParameters γ N}
    {M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ))}
    {T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜] JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))}
    {ε δ : ℝ} (F : OrdinalVariableUnitColouredCores P M T S ε δ) (hγ : IsSuccLimit γ) :
    OrdinalPrincipalCofinalSequence (Ordinal.omega0 ^ γ) where
  endpoint i := Ordinal.omega0 ^ P.sourceUnit (F.index i)
  strictMono := (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.comp F.selectedRank_strictMono
  principal i := Ordinal.principal_add_omega0_opow _
  limit i := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
    (Ordinal.omega0_pos.trans_le (F.selectedRank_large i)).ne'
  head_large := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
        (Ordinal.one_lt_omega0.trans_le (F.selectedRank_large 0))
  bound i := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (F.selectedRank_lt i)
  cofinal := P.power_sourceUnit_subsequence_cofinal hγ F.index F.strictMono

end OrdinalVariableUnitColouredCores

theorem ordinalVariableUnit_halfOpen_hasCPFP (γ : Ordinal.{u})
    (hP : Ordinal.Principal (· + ·) γ) (hω : Ordinal.omega0 < γ)
    (hcf : γ.cof = Cardinal.aleph0) :
    HasCPFP 𝕜 (JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))) 160 := by
  have hγ : IsSuccLimit γ := Ordinal.aleph0_le_cof.mp (by rw [hcf])
  intro T
  let S := ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))) - T
  let M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ)) :=
    (JLMS.exists_atomicDualModel (JLMS.scattered_subtype JLMS.scattered_ordinal _)).some
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖T‖ + ‖S‖) / (1 / 100 : ℝ))
  have hN' : ‖T‖ + ‖S‖ < N * (1 / 100 : ℝ) :=
    (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 100)).mp hN
  obtain ⟨P⟩ := exists_ordinalVariableUnitParameters γ hP hω hcf N
  obtain ⟨F⟩ := exists_ordinalVariableUnitColouredCores P M T S (by dsimp [S]; abel) hN'
    (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨J, R, hf, hJ, hR⟩ := F.selected_block_factorization hγ
  have h := ordinalCofinalBlocks_factorizationWith160 (F.cofinalBlockSequence hγ)
    (if F.colour then T else S) J R hf hJ hR
  cases hb : F.colour with
  | false => exact Or.inr (by simpa only [hb, Bool.false_eq_true, if_false] using h)
  | true => exact Or.inl (by simpa only [hb, if_true] using h)

theorem ordinalVariableUnit_hasUPFP (γ : Ordinal.{u})
    (hP : Ordinal.Principal (· + ·) γ) (hω : Ordinal.omega0 < γ)
    (hcf : γ.cof = Cardinal.aleph0) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) := by
  have h : HasUPFP 𝕜 (JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))) :=
    ⟨160, by norm_num, ordinalVariableUnit_halfOpen_hasCPFP γ hP hω hcf⟩
  have hinf : Ordinal.omega0 ≤ Ordinal.omega0 ^ γ := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
      (Ordinal.one_lt_omega0.le.trans hω.le)
  exact h.of_equiv (ordinalHalfOpenContinuousEquiv _ hinf)

theorem ordinalInitialOmegaOmega_hasUPFP (c : Cardinal.{u})
    (hc : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (c.ord ^ (Ordinal.omega0 ^ Ordinal.omega0))) := by
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)
  have hωκ : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hc
  have h := ordinalVariableUnit_hasUPFP (𝕜 := 𝕜) (c.ord * Ordinal.omega0 ^ Ordinal.omega0)
    (ordinal_higher_limit_rank_principal c.ord Ordinal.omega0_ne_zero)
    (hωκ.trans_le (Ordinal.le_mul_left _ (Ordinal.opow_pos _ Ordinal.omega0_pos)))
    (ordinal_higher_limit_rank_cof_limit hκ Ordinal.isSuccLimit_omega0 Ordinal.cof_omega0)
  have he : Ordinal.omega0 ^ (c.ord * Ordinal.omega0 ^ Ordinal.omega0) =
      c.ord ^ (Ordinal.omega0 ^ Ordinal.omega0) := by
    rw [Ordinal.opow_mul, ordinal_uncountable_initial_omega_power hc]
  exact h.of_equiv (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv

theorem proposition_3_1_variableUnit
    (γ : Ordinal.{0}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hcf : γ.cof = Cardinal.aleph0) :
    Proposition_3_1 𝕜 (Ordinal.omega0 ^ γ) := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) (Ordinal.omega0 ^ γ)) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (ordinalVariableUnit_hasUPFP (𝕜 := 𝕜) γ hP hω hcf).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

theorem proposition_3_1_initialOmegaOmega
    (c : Cardinal.{0}) (hc : Cardinal.aleph0 < c) :
    Proposition_3_1 𝕜 (c.ord ^ (Ordinal.omega0 ^ Ordinal.omega0)) := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) (c.ord ^ (Ordinal.omega0 ^ Ordinal.omega0))) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (ordinalInitialOmegaOmega_hasUPFP (𝕜 := 𝕜) c hc).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets
