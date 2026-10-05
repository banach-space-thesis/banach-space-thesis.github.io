import ThesisCommon.Analysis.FreeNatUltrafilterScalarCompression
import ThesisCommon.Analysis.ContinuousFunctionTensorMaps
import ThesisCommon.Analysis.CountableTotalDual

/-! Drewnowski's separable vector-valued scalarization theorem on genuine
C(ω*) spaces. The coefficient map is constructed by evaluating the given
operator on clopen-supported constants. Domain separability and a countable
total dual in the codomain are explicit; neither is silently omitted. -/
noncomputable section
open Set TopologicalSpace
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem exists_freeNatUltrafilter_vector_compression [SeparableSpace X]
    (hY : HasCountableTotalDual 𝕜 Y)
    (T : C(FreeNatUltrafilter, X) →L[𝕜] C(FreeNatUltrafilter, Y))
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ u : X →L[𝕜] Y,
      ‖u‖ ≤ ‖T‖ ∧ ∀ f : C(FreeNatUltrafilter, X),
      (∀ U, U ∉ FreeNatUltrafilter.basic B → f U = 0) →
      ∀ U ∈ FreeNatUltrafilter.basic B, T f U = u (f U) := by
  classical
  obtain ⟨M, hM, htotal⟩ := hY
  let φ := Set.enumerateCountable hM (0 : Y →L[𝕜] 𝕜)
  have hφ (y : Y) (hy : ∀ n, φ n y = 0) : y = 0 := by
    apply htotal y
    intro ψ hψ
    obtain ⟨n, hn⟩ := Set.subset_range_enumerate hM (0 : Y →L[𝕜] 𝕜) hψ
    exact hn ▸ hy n
  let x := denseSeq X
  let S (n : ℕ) : C(FreeNatUltrafilter, 𝕜) →L[𝕜] C(FreeNatUltrafilter, 𝕜) :=
    (ContinuousLinearMap.compLeftContinuous 𝕜 FreeNatUltrafilter (φ n.unpair.2)).comp
      (T.comp (continuousFunctionTensor (x n.unpair.1)))
  obtain ⟨B, hB, hBA, c, hc⟩ := exists_freeNatUltrafilter_countable_scalar_compression S hA
  obtain ⟨U₀, hU₀⟩ := FreeNatUltrafilter.exists_mem hB
  change U₀ ∈ FreeNatUltrafilter.basic B at hU₀
  let χ : C(FreeNatUltrafilter, 𝕜) :=
    continuousFunctionMask (𝕜 := 𝕜) (FreeNatUltrafilter.basic B)
      (FreeNatUltrafilter.isClopen_basic B) (ContinuousMap.const _ 1)
  let u : X →L[𝕜] Y := (ContinuousMap.evalCLM 𝕜 U₀).comp
    (T.comp (continuousFunctionScalarMultiply χ))
  have hχ (U : FreeNatUltrafilter) : χ U = if U ∈ FreeNatUltrafilter.basic B then 1 else 0 := rfl
  have hχnorm : ‖χ‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro U
    rw [hχ]
    split_ifs <;> simp
  have hunorm : ‖u‖ ≤ ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro z
    change ‖T (continuousFunctionScalarMultiply χ z) U₀‖ ≤ ‖T‖ * ‖z‖
    apply (T (continuousFunctionScalarMultiply χ z)).norm_coe_le_norm U₀ |>.trans
    apply (T.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
    apply ((continuousFunctionScalarMultiply (X := X) χ).le_opNorm z).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg z) |>.trans_eq (one_mul _)
    exact (norm_continuousFunctionScalarMultiply_le (X := X) χ).trans hχnorm
  have htest (m n : ℕ) (f : C(FreeNatUltrafilter, 𝕜))
      (hf : ∀ U, U ∉ FreeNatUltrafilter.basic B → f U = 0)
      (U : FreeNatUltrafilter) (hU : U ∈ FreeNatUltrafilter.basic B) :
      φ n (T (continuousFunctionTensor (x m) f) U) = c (Nat.pair m n) * f U := by
    simpa only [S, Nat.unpair_pair, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compLeftContinuous_apply] using hc (Nat.pair m n) f hf U hU
  have hcoef (m n : ℕ) : φ n (u (x m)) = c (Nat.pair m n) := by
    have h := htest m n χ (by intro U hU; rw [hχ, if_neg hU]) U₀ hU₀
    simpa only [hχ, if_pos hU₀, mul_one] using h
  have hseq (m : ℕ) (f : C(FreeNatUltrafilter, 𝕜))
      (hf : ∀ U, U ∉ FreeNatUltrafilter.basic B → f U = 0)
      (U : FreeNatUltrafilter) (hU : U ∈ FreeNatUltrafilter.basic B) :
      T (continuousFunctionTensor (x m) f) U = f U • u (x m) := by
    apply sub_eq_zero.mp
    apply hφ
    intro n
    rw [map_sub, map_smul, hcoef, htest m n f hf U hU, smul_eq_mul, mul_comm, sub_self]
  have hall (z : X) (f : C(FreeNatUltrafilter, 𝕜))
      (hf : ∀ U, U ∉ FreeNatUltrafilter.basic B → f U = 0)
      (U : FreeNatUltrafilter) (hU : U ∈ FreeNatUltrafilter.basic B) :
      T (continuousFunctionTensor z f) U = f U • u z := by
    have he := (denseRange_denseSeq X).equalizer
      (((ContinuousMap.evalCLM 𝕜 U).comp (T.comp
        (continuousFunctionScalarMultiply f))).continuous)
      ((continuous_const : Continuous (fun _ : X => f U)).smul u.continuous)
      (funext fun m => hseq m f hf U hU)
    exact congrFun he z
  refine ⟨B, hB, hBA, u, hunorm, ?_⟩
  intro f hf U hU
  let P : C(FreeNatUltrafilter, X) →L[𝕜] C(FreeNatUltrafilter, X) :=
    continuousFunctionMask (𝕜 := 𝕜) (FreeNatUltrafilter.basic B)
      (FreeNatUltrafilter.isClopen_basic B)
  let L : C(FreeNatUltrafilter, X) →L[𝕜] Y :=
    (ContinuousMap.evalCLM 𝕜 U).comp (T.comp P)
  let R : C(FreeNatUltrafilter, X) →L[𝕜] Y :=
    u.comp ((ContinuousMap.evalCLM 𝕜 U).comp P)
  have hLR : L = R := by
    apply freeNatUltrafilter_operator_ext_of_tensors
    intro z g
    let g' : C(FreeNatUltrafilter, 𝕜) :=
      continuousFunctionMask (𝕜 := 𝕜) (FreeNatUltrafilter.basic B)
        (FreeNatUltrafilter.isClopen_basic B) g
    have hg' (V : FreeNatUltrafilter) (hV : V ∉ FreeNatUltrafilter.basic B) : g' V = 0 := by
      simp only [g', continuousFunctionMask_apply, if_neg hV]
    have hP : P (continuousFunctionTensor z g) = continuousFunctionTensor z g' := by
      ext V
      simp only [P, g', continuousFunctionMask_apply, continuousFunctionTensor_apply]
      split_ifs <;> simp
    change T (P (continuousFunctionTensor z g)) U =
      u (P (continuousFunctionTensor z g) U)
    rw [hP, continuousFunctionTensor_apply, map_smul]
    exact hall z g' hg' U hU
  have hPf : P f = f := by
    ext V
    simp only [P, continuousFunctionMask_apply]
    split_ifs with hV
    · rfl
    · exact (hf V hV).symm
  have he := congrArg (fun S : C(FreeNatUltrafilter, X) →L[𝕜] Y => S f) hLR
  change T (P f) U = u (P f U) at he
  simpa only [hPf] using he

end ThesisCommon
