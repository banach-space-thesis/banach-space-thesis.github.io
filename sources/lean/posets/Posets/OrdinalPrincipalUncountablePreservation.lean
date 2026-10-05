import Posets.OrdinalTransfiniteSelectedFactorization
import Posets.OrdinalTransfiniteAssemblyBridge
import Posets.OrdinalPrincipalInitialRankPreservation
import Posets.OrdinalVariableUnitPreservation

/-! Preservation at all additive-principal ranks, including uncountable cofinality. -/

noncomputable section
open Set Order Topology
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000

theorem ordinalPrincipalNoninitialUncountable_hasCPFP
    (γ : Ordinal.{0}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hc : Cardinal.aleph0 < γ.cof)
    (hgap : γ.cof.ord < γ) :
    HasCPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) 1280 := by
  intro T
  let S := ContinuousLinearMap.id 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) - T
  obtain ⟨N, R, hn, hF⟩ := exists_ordinalTransfiniteCorrectedColouredCores γ hP hc hgap T S
    (by dsimp [S]; abel) (by norm_num : (0 : ℝ) < 1/100) (by norm_num : (0 : ℝ) < 1/100)
  obtain ⟨F⟩ := hF
  let hγ := Ordinal.aleph0_le_cof.mp hc.le
  let P := R.paddedSequence hγ
  let T₀ := JLMS.ordinalZeroOperator (Ordinal.omega0 ^ γ)
    (ordinalCeilingCorrectedLeft P.blockMap P.blockMap_strictMono P.blockMap_endpoint T)
  let S₀ := JLMS.ordinalZeroOperator (Ordinal.omega0 ^ γ)
    (ordinalCeilingCorrectedRight P.blockMap P.blockMap_strictMono P.blockMap_endpoint S)
  have hreg : γ.cof.IsRegular := Cardinal.isRegular_cof hγ
  let Q := R.selectedTargetSequence hreg (by omega) hγ F.index F.injective
  let A := if F.colour then T else S
  have hW : (if F.colour then T₀ else S₀) = ordinalCeilingCorrectedCZero
      P.blockMap P.blockMap_strictMono P.blockMap_endpoint F.colour A := by
    cases hb : F.colour <;> simp only [A, hb, Bool.false_eq_true, if_false, if_true] <;> rfl
  obtain ⟨J, L, hf, hJ, hL⟩ := F.selected_factorization hreg A hW
  have hΓ : Ordinal.omega0 ≤ Ordinal.omega0 ^ γ := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
      (Ordinal.one_lt_omega0.trans hω).le
  have h := ordinalTransfiniteBlocks_full_factorizationWith1280 Q hΓ A J L hf hJ hL
  cases hb : F.colour with
  | false => exact Or.inr (by simpa only [A, hb, Bool.false_eq_true, if_false] using h)
  | true => exact Or.inl (by simpa only [A, hb, if_true] using h)

theorem ordinalPrincipalUncountableCofinality_hasUPFP
    (γ : Ordinal.{0}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hc : Cardinal.aleph0 < γ.cof) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) := by
  by_cases hγ : γ = γ.cof.ord
  · exact ordinalPrincipalInitialRank_hasUPFP γ hc hγ
  · exact ⟨1280, by norm_num, ordinalPrincipalNoninitialUncountable_hasCPFP γ hP hω hc
      (lt_of_le_of_ne (Ordinal.ord_cof_le γ) (Ne.symm hγ))⟩

theorem ordinalPrincipal_hasUPFP
    (γ : Ordinal.{0}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) := by
  by_cases hcf : γ.cof = Cardinal.aleph0
  · exact ordinalVariableUnit_hasUPFP γ hP hω hcf
  · have hlim := Ordinal.isSuccLimit_of_principal_add (Ordinal.one_lt_omega0.trans hω) hP
    have hc : Cardinal.aleph0 < γ.cof :=
      lt_of_le_of_ne (Ordinal.aleph0_le_cof.mpr hlim) (Ne.symm hcf)
    exact ordinalPrincipalUncountableCofinality_hasUPFP γ hP hω hc

end Posets

