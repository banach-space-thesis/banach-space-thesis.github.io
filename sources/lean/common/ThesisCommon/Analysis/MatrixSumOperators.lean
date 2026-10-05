import ThesisCommon.Analysis.MatrixBlockOperators

/-! The genuine bounded product of growing finite matrix blocks. Diagonal
action below is required on every vector of this nonseparable product. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
attribute [local instance] Classical.propDecidable

instance (priority := 2000) finiteMatrixBlockModule (p : BanachExponent) (N : ℕ) :
    Module 𝕜 (FiniteMatrixBlock 𝕜 p N) :=
  (ContinuousLinearMap.toNormedSpace : NormedSpace 𝕜 (FiniteMatrixBlock 𝕜 p N)).toModule

abbrev FiniteMatrixSum (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :=
  lp (fun n : ℕ => FiniteMatrixBlock 𝕜 p (n + 1)) ∞

/- These named instances expose the existing lp structures directly and
avoid exploring alternative ring structures on the nested operator product. -/
instance finiteMatrixSumNormedAddCommGroup (p : BanachExponent) :
    NormedAddCommGroup (FiniteMatrixSum 𝕜 p) := lp.normedAddCommGroup

instance finiteMatrixSumNormedSpace (p : BanachExponent) :
    NormedSpace 𝕜 (FiniteMatrixSum 𝕜 p) := lp.instNormedSpace

instance (priority := 2000) finiteMatrixSumAddCommMonoid (p : BanachExponent) :
    AddCommMonoid (FiniteMatrixSum 𝕜 p) :=
  (finiteMatrixSumNormedAddCommGroup (𝕜 := 𝕜) p).toAddCommGroup.toAddCommMonoid

instance (priority := 2000) finiteMatrixSumModule (p : BanachExponent) :
    Module 𝕜 (FiniteMatrixSum 𝕜 p) :=
  (finiteMatrixSumNormedSpace (𝕜 := 𝕜) p).toModule

def matrixSumCoordinate (p : BanachExponent) (n : ℕ) :
    FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixBlock 𝕜 p (n + 1) :=
  LinearMap.mkContinuous
    { toFun x := x n
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    1 (fun x => by simpa only [one_mul] using lp.norm_apply_le_norm ENNReal.top_ne_zero x n)

def matrixSumSingle (p : BanachExponent) (n : ℕ) :
    FiniteMatrixBlock 𝕜 p (n + 1) →L[𝕜] FiniteMatrixSum 𝕜 p :=
  lp.singleContinuousLinearMap 𝕜 (fun k => FiniteMatrixBlock 𝕜 p (k + 1)) ∞ n

set_option maxHeartbeats 800000 in
def matrixSumMask (p : BanachExponent) (I : Set ℕ) :
    FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p := by
  classical
  let mask (x : FiniteMatrixSum 𝕜 p) : FiniteMatrixSum 𝕜 p :=
    ⟨fun n => if n ∈ I then x n else 0, memℓp_infty ⟨‖x‖, by
      rintro _ ⟨n, rfl⟩
      by_cases hn : n ∈ I
      · simpa only [if_pos hn] using lp.norm_apply_le_norm ENNReal.top_ne_zero x n
      · simp only [if_neg hn, norm_zero]; exact norm_nonneg _⟩⟩
  refine LinearMap.mkContinuous
    { toFun := mask
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro x y
    apply lp.ext
    funext n
    change (if n ∈ I then x n + y n else 0) =
      (if n ∈ I then x n else 0) + (if n ∈ I then y n else 0)
    by_cases hn : n ∈ I
    · simp only [if_pos hn]
    · simp only [if_neg hn, add_zero]
  · intro a x
    apply lp.ext
    funext n
    change (if n ∈ I then a • x n else 0) = a • (if n ∈ I then x n else 0)
    by_cases hn : n ∈ I
    · simp only [if_pos hn]
    · simp only [if_neg hn, smul_zero]
  · intro x
    change ‖mask x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    apply lp.norm_le_of_forall_le (norm_nonneg x)
    intro n
    change ‖if n ∈ I then x n else 0‖ ≤ ‖x‖
    by_cases hn : n ∈ I
    · simpa only [if_pos hn] using lp.norm_apply_le_norm ENNReal.top_ne_zero x n
    · simp only [if_neg hn, norm_zero]; exact norm_nonneg _

@[simp] theorem matrixSumMask_apply (p : BanachExponent) (I : Set ℕ)
    (x : FiniteMatrixSum 𝕜 p) (n : ℕ) :
    matrixSumMask p I x n = if n ∈ I then x n else 0 := by
  classical
  rfl

set_option maxHeartbeats 800000 in
theorem norm_matrixSumMask_le (p : BanachExponent) (I : Set ℕ) :
    ‖matrixSumMask (𝕜 := 𝕜) p I‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply lp.norm_le_of_forall_le (norm_nonneg x)
  intro n
  rw [matrixSumMask_apply]
  by_cases hn : n ∈ I
  · simpa only [if_pos hn] using lp.norm_apply_le_norm ENNReal.top_ne_zero x n
  · simp only [if_neg hn, norm_zero]; exact norm_nonneg _

def matrixSumSupport (p : BanachExponent) (I : Set ℕ) : Submodule 𝕜 (FiniteMatrixSum 𝕜 p) where
  carrier := {x | ∀ n ∉ I, x n = 0}
  zero_mem' := by intro n hn; rfl
  add_mem' := by intro x y hx hy n hn; change x n + y n = 0; rw [hx n hn, hy n hn, add_zero]
  smul_mem' := by intro a x hx n hn; change a • x n = 0; rw [hx n hn, smul_zero]

/-- Actual coordinatewise action; unit-vector entries alone do not define a diagonal operator here. -/
def IsMatrixSumDiagonal (p : BanachExponent)
    (D : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p) : Prop :=
  ∃ F : ∀ n : ℕ, FiniteMatrixBlock 𝕜 p (n + 1) →L[𝕜] FiniteMatrixBlock 𝕜 p (n + 1),
    ∀ x n, D x n = F n (x n)

end ThesisCommon
