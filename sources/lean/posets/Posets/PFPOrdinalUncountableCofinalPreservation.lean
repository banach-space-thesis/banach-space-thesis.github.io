import Posets.PFPOrdinalTransfiniteFactorAssembly
import Posets.PFPTransfiniteGapSelection
import Posets.TransfiniteCZeroInsertion
import Posets.OrdinalTransfiniteAssemblyBridge

/-! Unconditional uniform preservation at every noninitial additive-
principal rank of uncountable cofinality. An actual cofinal subfamily of
the selected target blocks supplies the fixed coefficient model. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2400000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace

theorem pfpOrdinalUncountableCofinal_hasCPFP
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hc : Cardinal.aleph0 < γ.cof) (hgap : γ.cof.ord < γ) :
    HasCPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) 1280 := by
  intro T
  let hγ : IsSuccLimit γ := Ordinal.aleph0_le_cof.mp hc.le
  obtain ⟨N, R, ⟨F⟩⟩ := exists_pfpOrdinalTransfinitePaddedSelection γ hP hc hgap T
  obtain ⟨J, V, hf, hJn, hVn⟩ := F.exists_block_factorization
  let P := R.baseTargetSequence (by omega) hγ
  have hregular : γ.cof.IsRegular := Cardinal.isRegular_cof hγ
  obtain ⟨r, hr, hkr, hri, _, hrgap⟩ :=
    PFPTransfinite.exists_regularOrdinal_injective_principal_gap_selection hregular P.endpoint
      P.strictMono P.principal
      (fun i => (Ordinal.opow_pos (R.unit i) Ordinal.omega0_pos).ne') F.index F.injective
  let Q : OrdinalPrincipalTransfiniteSequence γ.cof.ord (Ordinal.omega0 ^ γ) := {
    infinite := P.infinite
    endpoint := fun i => P.endpoint (F.index (r i))
    strictMono := P.strictMono.comp hkr
    principal := fun i => P.principal (F.index (r i))
    head_large := P.head_large.trans_le (P.strictMono.monotone
      (show P.zeroIndex ≤ F.index (r P.zeroIndex) from Ordinal.zero_le _))
    bound := fun i => P.bound (F.index (r i))
    cofinal := fun β hβ => by
      obtain ⟨i, hi⟩ := P.cofinal β hβ
      exact ⟨i, hi.trans_le (P.strictMono.monotone (hri i).le)⟩
    gap := hrgap }
  let E := fun i : Iio γ.cof.ord => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i))
  let insert := TransfiniteCZero.cZeroSum_insertCLM (𝕜 := 𝕜) (E := E) r hr
  let read := JLMS.CZeroSum.comapCLM (𝕜 := 𝕜) (E := E) r hr
  have hir : read.comp insert = ContinuousLinearMap.id 𝕜 (JLMS.CZeroSum 𝕜 (fun i => E (r i))) := by
    apply ContinuousLinearMap.ext
    intro f
    apply JLMS.CZeroSum.ext
    intro i
    exact TransfiniteCZero.cZeroSum_insertCLM_apply_selected (𝕜 := 𝕜) (E := E) r hr f i
  have hin : ‖insert‖ ≤ 1 := TransfiniteCZero.norm_cZeroSum_insertCLM_le (𝕜 := 𝕜) (E := E) r hr
  have hrn : ‖read‖ ≤ 1 := TransfiniteCZero.norm_cZeroSum_comapCLM_le (𝕜 := 𝕜) (E := E) r hr
  let A := if F.colour then T else ContinuousLinearMap.id 𝕜 _ - T
  have hf' : (read.comp V).comp (A.comp (J.comp insert)) = ContinuousLinearMap.id 𝕜 _ := by
    calc
      _ = read.comp ((V.comp (A.comp J)).comp insert) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = read.comp insert := by rw [hf, ContinuousLinearMap.id_comp]
      _ = _ := hir
  have hJ' : ‖J.comp insert‖ ≤ 1 :=
    (J.opNorm_comp_le insert).trans ((mul_le_mul hJn hin (norm_nonneg insert) zero_le_one).trans_eq (one_mul _))
  have hV' : ‖read.comp V‖ ≤ 5 :=
    (read.opNorm_comp_le V).trans ((mul_le_mul hrn hVn (norm_nonneg V) zero_le_one).trans_eq (one_mul _))
  have hΓ : Ordinal.omega0 ≤ Ordinal.omega0 ^ γ :=
    (Ordinal.omega0_le_of_isSuccLimit hγ).trans (Ordinal.right_le_opow γ Ordinal.one_lt_omega0)
  have hfFull := ordinalTransfiniteBlocks_full_factorizationWith1280 Q hΓ A
    (J.comp insert) (read.comp V) hf' hJ' hV'
  cases hb : F.colour with
  | false => exact Or.inr (by simpa only [A, hb, Bool.false_eq_true, if_false] using hfFull)
  | true => exact Or.inl (by simpa only [A, hb, if_true] using hfFull)

theorem pfpOrdinalUncountableCofinal_hasUPFP
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hc : Cardinal.aleph0 < γ.cof) (hgap : γ.cof.ord < γ) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) :=
  ⟨1280, by norm_num, pfpOrdinalUncountableCofinal_hasCPFP γ hP hc hgap⟩

end Posets
