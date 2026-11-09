import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.CZeroOperators

/-! Contractive block retractions on actual sequence spaces.
Read selected outer coordinates and apply a contractive map in each block;
the inverse insertion uses the corresponding right inverses. These maps
cover both full inner-coordinate restrictions and single inner coordinates
in the self-similar diagonal reduction of UPFP Section 5.
-/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def lpBlockRead (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ)
    (F : ℕ → Y →L[𝕜] X) (hF : ∀ k, ‖F k‖ ≤ 1) :
    lp (fun _ : ℕ => Y) q →L[𝕜] lp (fun _ : ℕ => X) q :=
  (lpDiagonal q F 1 zero_le_one hF).comp (lpRestrict q e)

def lpBlockInsert (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ)
    (G : ℕ → X →L[𝕜] Y) (hG : ∀ k, ‖G k‖ ≤ 1) :
    lp (fun _ : ℕ => X) q →L[𝕜] lp (fun _ : ℕ => Y) q :=
  (lpExtend q e).comp (lpDiagonal q G 1 zero_le_one hG)

@[simp] theorem lpBlockRead_apply (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ)
    (F : ℕ → Y →L[𝕜] X) (hF) (x : lp (fun _ : ℕ => Y) q) (k : ℕ) :
    lpBlockRead q e F hF x k = F k (x (e k)) := rfl

@[simp] theorem lpBlockInsert_apply_image (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ)
    (G : ℕ → X →L[𝕜] Y) (hG) (x : lp (fun _ : ℕ => X) q) (k : ℕ) :
    lpBlockInsert q e G hG x (e k) = G k (x k) := by
  exact lpExtend_apply_image (𝕜 := 𝕜) e _ k

theorem norm_lpBlockRead_le (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ)
    (F : ℕ → Y →L[𝕜] X) (hF) : ‖lpBlockRead q e F hF‖ ≤ 1 := by
  calc
    _ ≤ ‖lpDiagonal q F 1 zero_le_one hF‖ * ‖lpRestrict (𝕜 := 𝕜) (X := Y) q e‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_lpDiagonal_le F 1 zero_le_one hF)
      (norm_lpRestrict_le e) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem norm_lpBlockInsert_le (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ)
    (G : ℕ → X →L[𝕜] Y) (hG) : ‖lpBlockInsert q e G hG‖ ≤ 1 := by
  calc
    _ ≤ ‖lpExtend (𝕜 := 𝕜) (X := Y) q e‖ * ‖lpDiagonal q G 1 zero_le_one hG‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_lpExtend_le e)
      (norm_lpDiagonal_le G 1 zero_le_one hG) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem lpBlockRead_comp_insert (q : ℝ≥0∞) [Fact (1 ≤ q)] (e : ℕ ↪ ℕ)
    (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG)
    (hFG : ∀ k, (F k).comp (G k) = ContinuousLinearMap.id 𝕜 X) :
    (lpBlockRead q e F hF).comp (lpBlockInsert q e G hG) =
      ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => X) q) := by
  ext x k
  change F k (lpBlockInsert q e G hG x (e k)) = x k
  rw [lpBlockInsert_apply_image]
  exact DFunLike.congr_fun (hFG k) (x k)

def cZeroBlockRead (e : ℕ ↪ ℕ)
    (F : ℕ → Y →L[𝕜] X) (hF : ∀ k, ‖F k‖ ≤ 1) : CZeroSum Y →L[𝕜] CZeroSum X :=
  (cZeroDiagonal F 1 zero_le_one hF).comp (cZeroRestrict e)

def cZeroBlockInsert (e : ℕ ↪ ℕ)
    (G : ℕ → X →L[𝕜] Y) (hG : ∀ k, ‖G k‖ ≤ 1) : CZeroSum X →L[𝕜] CZeroSum Y :=
  (cZeroExtend e).comp (cZeroDiagonal G 1 zero_le_one hG)

@[simp] theorem cZeroBlockRead_apply (e : ℕ ↪ ℕ) (F : ℕ → Y →L[𝕜] X) (hF)
    (x : CZeroSum Y) (k : ℕ) : cZeroBlockRead e F hF x k = F k (x (e k)) := rfl

@[simp] theorem cZeroBlockInsert_apply_image (e : ℕ ↪ ℕ) (G : ℕ → X →L[𝕜] Y) (hG)
    (x : CZeroSum X) (k : ℕ) : cZeroBlockInsert e G hG x (e k) = G k (x k) := by
  exact cZeroExtend_apply_image (𝕜 := 𝕜) e _ k

theorem norm_cZeroBlockRead_le (e : ℕ ↪ ℕ) (F : ℕ → Y →L[𝕜] X) (hF) :
    ‖cZeroBlockRead e F hF‖ ≤ 1 := by
  calc
    _ ≤ ‖cZeroDiagonal F 1 zero_le_one hF‖ * ‖cZeroRestrict (𝕜 := 𝕜) (X := Y) e‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_cZeroDiagonal_le F 1 zero_le_one hF)
      (norm_cZeroRestrict_le e) (norm_nonneg (cZeroRestrict (𝕜 := 𝕜) (X := Y) e)) zero_le_one
    _ = 1 := one_mul _

theorem norm_cZeroBlockInsert_le (e : ℕ ↪ ℕ) (G : ℕ → X →L[𝕜] Y) (hG) :
    ‖cZeroBlockInsert e G hG‖ ≤ 1 := by
  calc
    _ ≤ ‖cZeroExtend (𝕜 := 𝕜) (X := Y) e‖ * ‖cZeroDiagonal G 1 zero_le_one hG‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_cZeroExtend_le e)
      (norm_cZeroDiagonal_le G 1 zero_le_one hG) (norm_nonneg (cZeroDiagonal G 1 zero_le_one hG)) zero_le_one
    _ = 1 := one_mul _

theorem cZeroBlockRead_comp_insert (e : ℕ ↪ ℕ)
    (F : ℕ → Y →L[𝕜] X) (G : ℕ → X →L[𝕜] Y) (hF hG)
    (hFG : ∀ k, (F k).comp (G k) = ContinuousLinearMap.id 𝕜 X) :
    (cZeroBlockRead e F hF).comp (cZeroBlockInsert e G hG) =
      ContinuousLinearMap.id 𝕜 (CZeroSum X) := by
  ext x k
  change F k (cZeroBlockInsert e G hG x (e k)) = x k
  rw [cZeroBlockInsert_apply_image]
  exact DFunLike.congr_fun (hFG k) (x k)

end ThesisCommon
