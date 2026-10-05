import Posets.AlspachCounterexampleProbability
import Posets.AlspachCounterexampleSurjection
import JLMS.AtomicDual

/-! Actual evaluation operators for Alspach probability families. Atomic
duality and the one-third forest estimate prove surjectivity, without an
assumed right inverse or a surjectivity field in the construction data. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open scoped ZeroAtInfty
open JLMS
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace L] [CompactSpace L]
local instance alspachEvaluationDualGroup : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance alspachEvaluationDualSpace : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

def alspachEvaluationValue (r : L → (CZero 𝕜 K →L[𝕜] 𝕜))
    (hcont : ∀ f : CZero 𝕜 K, Continuous (fun l => r l f))
    (f : CZero 𝕜 K) : CZero 𝕜 L :=
  ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty ⟨fun l => r l f, hcont f⟩

def alspachEvaluation (r : L → (CZero 𝕜 K →L[𝕜] 𝕜))
    (hcont : ∀ f : CZero 𝕜 K, Continuous (fun l => r l f))
    (hr : ∀ l, ‖r l‖ ≤ 1) : CZero 𝕜 K →L[𝕜] CZero 𝕜 L :=
  ({ toFun := alspachEvaluationValue r hcont
     map_add' f g := by ext l; exact (r l).map_add f g
     map_smul' c f := by ext l; exact (r l).map_smul c f } :
    CZero 𝕜 K →ₗ[𝕜] CZero 𝕜 L).mkContinuous 1 (fun f => by
      simp only [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
      intro l
      exact ((r l).le_opNorm f).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hr l) (norm_nonneg f)))

@[simp] theorem alspachEvaluation_apply (r : L → (CZero 𝕜 K →L[𝕜] 𝕜))
    (hcont : ∀ f : CZero 𝕜 K, Continuous (fun l => r l f))
    (hr : ∀ l, ‖r l‖ ≤ 1) (f : CZero 𝕜 K) (l : L) :
    alspachEvaluation r hcont hr f l = r l f := rfl

theorem alspachEvaluation_norm_le (r : L → (CZero 𝕜 K →L[𝕜] 𝕜))
    (hcont : ∀ f : CZero 𝕜 K, Continuous (fun l => r l f))
    (hr : ∀ l, ‖r l‖ ≤ 1) : ‖alspachEvaluation r hcont hr‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro l
  simpa only [one_mul] using (r l).le_of_opNorm_le (hr l) f

theorem alspachEvaluation_adjoint_coordinates (M : AtomicDualModel 𝕜 L)
    (r : L → (CZero 𝕜 K →L[𝕜] 𝕜))
    (hcont : ∀ f : CZero 𝕜 K, Continuous (fun l => r l f))
    (hr : ∀ l, ‖r l‖ ≤ 1) :
    (banachAdjoint (alspachEvaluation r hcont hr)).comp
        M.representation.symm.toLinearIsometry.toContinuousLinearMap =
      alspachSynthesis (𝕜 := 𝕜) r 1 hr := by
  apply alspach_lp_ext
  intro l
  change banachAdjoint (alspachEvaluation r hcont hr)
    (M.representation.symm (lp.single 1 l 1)) = alspachSynthesis (𝕜 := 𝕜) r 1 hr (lp.single 1 l 1)
  rw [M.pointMass, alspachSynthesis_single, one_smul]
  apply ContinuousLinearMap.ext
  intro f
  rfl

theorem alspachEvaluation_surjective (M : AtomicDualModel 𝕜 L)
    (r : L → (CZero 𝕜 K →L[𝕜] 𝕜))
    (hcont : ∀ f : CZero 𝕜 K, Continuous (fun l => r l f))
    (hr : ∀ l, ‖r l‖ ≤ 1) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ a : lp (fun _ : L => 𝕜) 1,
      c * ‖a‖ ≤ ‖alspachSynthesis (𝕜 := 𝕜) r 1 hr a‖) :
    Function.Surjective (alspachEvaluation r hcont hr) := by
  apply alspach_surjective_of_adjoint_lower _ hc
  intro φ
  have he := DFunLike.congr_fun (alspachEvaluation_adjoint_coordinates M r hcont hr)
    (M.representation φ)
  change banachAdjoint (alspachEvaluation r hcont hr) (M.representation.symm (M.representation φ)) =
    alspachSynthesis (𝕜 := 𝕜) r 1 hr (M.representation φ) at he
  rw [M.representation.symm_apply_apply] at he
  have h := hlower (M.representation φ)
  rw [M.representation.norm_map, ← he] at h
  exact h

theorem alspachForestEvaluation_surjective (MK : AtomicDualModel 𝕜 K)
    (ML : AtomicDualModel 𝕜 L)
    (F : AlspachForestRows 𝕜 L (lp (fun _ : K => 𝕜) 1))
    (hcont : ∀ f : CZero 𝕜 K,
      Continuous (fun l => MK.representation.symm (F.row l) f)) :
    Function.Surjective (alspachEvaluation
      (fun l => MK.representation.symm (F.row l)) hcont
      (fun l => by simpa only [MK.representation.symm.norm_map] using F.row_norm_le l)) := by
  let r (l : L) := MK.representation.symm (F.row l)
  have hr (l : L) : ‖r l‖ ≤ 1 := by
    simpa only [r, MK.representation.symm.norm_map] using F.row_norm_le l
  apply alspachEvaluation_surjective ML r hcont hr (c := 1 / 3) (by norm_num)
  have he : alspachSynthesis (𝕜 := 𝕜) r 1 hr =
      MK.representation.symm.toLinearIsometry.toContinuousLinearMap.comp F.synthesis := by
    apply alspach_lp_ext
    intro l
    simp only [alspachSynthesis_single, one_smul, ContinuousLinearMap.comp_apply,
      AlspachForestRows.synthesis_single, r]
    rfl
  intro a
  rw [he, ContinuousLinearMap.comp_apply]
  change 1 / 3 * ‖a‖ ≤ ‖MK.representation.symm (F.synthesis a)‖
  rw [MK.representation.symm.norm_map]
  exact F.synthesis_lower a

end Posets

