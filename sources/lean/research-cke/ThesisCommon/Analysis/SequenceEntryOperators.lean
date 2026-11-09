import ThesisCommon.Analysis.SequenceCoordinates
import ThesisCommon.Analysis.CZeroSingles
import ThesisCommon.Analysis.LpDiagonal
import ThesisCommon.Analysis.CZeroDiagonal

/-! Actual operator entries, bounded diagonal parts, and compression formulas.
The definition of a diagonal part constructs a whole operator on the sequence
space; it does not assert matrix determination for the original operator.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_lpSingleCLM_le (n : ℕ) :
    ‖lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [lp.singleContinuousLinearMap_apply, one_mul,
    lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))]
  exact le_rfl

theorem norm_cZeroSingleCLM_le (n : ℕ) : ‖cZeroSingleCLM (𝕜 := 𝕜) (X := X) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [cZeroSingleCLM_apply, one_mul] using norm_cZeroSingle_le n x

/-- The genuine (m,n) coordinate entry of an lp operator. -/
def lpEntry (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    (m n : ℕ) : X →L[𝕜] X :=
  ((lpCoordinate p m).comp T).comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p n)

@[simp] theorem lpEntry_apply (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    (m n : ℕ) (x : X) : lpEntry T m n x = T (lp.single p n x) m := rfl

theorem norm_lpEntry_le (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    (m n : ℕ) : ‖lpEntry T m n‖ ≤ ‖T‖ := by
  have hr : ‖(lpCoordinate (𝕜 := 𝕜) (X := X) p m).comp T‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖lpCoordinate (𝕜 := 𝕜) (X := X) p m‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_lpCoordinate_le p m) (norm_nonneg T)
      _ = ‖T‖ := one_mul _
  calc
    _ ≤ ‖(lpCoordinate (𝕜 := 𝕜) (X := X) p m).comp T‖ *
        ‖lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p n‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T‖ * 1 := mul_le_mul hr (norm_lpSingleCLM_le n) (norm_nonneg _) (norm_nonneg T)
    _ = ‖T‖ := mul_one _

/-- The genuine (m,n) coordinate entry on c₀. -/
def cZeroEntry (T : CZeroSum X →L[𝕜] CZeroSum X) (m n : ℕ) : X →L[𝕜] X :=
  ((cZeroCoordinate m).comp T).comp (cZeroSingleCLM n)

@[simp] theorem cZeroEntry_apply (T : CZeroSum X →L[𝕜] CZeroSum X)
    (m n : ℕ) (x : X) : cZeroEntry T m n x = T (cZeroSingle n x) m := rfl

theorem norm_cZeroEntry_le (T : CZeroSum X →L[𝕜] CZeroSum X) (m n : ℕ) :
    ‖cZeroEntry T m n‖ ≤ ‖T‖ := by
  have hr : ‖(cZeroCoordinate (𝕜 := 𝕜) (X := X) m).comp T‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖cZeroCoordinate (𝕜 := 𝕜) (X := X) m‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_cZeroCoordinate_le m) (norm_nonneg T)
      _ = ‖T‖ := one_mul _
  calc
    _ ≤ ‖(cZeroCoordinate (𝕜 := 𝕜) (X := X) m).comp T‖ * ‖cZeroSingleCLM (𝕜 := 𝕜) (X := X) n‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T‖ * 1 := mul_le_mul hr (norm_cZeroSingleCLM_le n)
      (norm_nonneg (cZeroSingleCLM (𝕜 := 𝕜) (X := X) n)) (norm_nonneg T)
    _ = ‖T‖ := mul_one _

/-- The bounded diagonal operator with the same diagonal entries as T. -/
def lpDiagonalPart (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) :
    lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p :=
  lpDiagonal p (fun n => lpEntry T n n) ‖T‖ (norm_nonneg T) (fun n => norm_lpEntry_le T n n)

@[simp] theorem lpDiagonalPart_apply (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    (x : lp (fun _ : ℕ => X) p) (n : ℕ) : lpDiagonalPart T x n = lpEntry T n n (x n) := rfl

theorem isLpDiagonal_lpDiagonalPart (T : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) :
    IsLpDiagonal (lpDiagonalPart T) := ⟨fun n => lpEntry T n n, fun _ _ => rfl⟩

def cZeroDiagonalPart (T : CZeroSum X →L[𝕜] CZeroSum X) : CZeroSum X →L[𝕜] CZeroSum X :=
  cZeroDiagonal (fun n => cZeroEntry T n n) ‖T‖ (norm_nonneg T) (fun n => norm_cZeroEntry_le T n n)

@[simp] theorem cZeroDiagonalPart_apply (T : CZeroSum X →L[𝕜] CZeroSum X)
    (x : CZeroSum X) (n : ℕ) : cZeroDiagonalPart T x n = cZeroEntry T n n (x n) := rfl

theorem isCZeroDiagonal_cZeroDiagonalPart (T : CZeroSum X →L[𝕜] CZeroSum X) :
    IsCZeroDiagonal (cZeroDiagonalPart T) := ⟨fun n => cZeroEntry T n n, fun _ _ => rfl⟩

end ThesisCommon
