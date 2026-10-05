import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.SequenceCoordinates
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Concrete finite matrix blocks with the ℓp operator norm. Coordinate
matrix units and rectangular block maps are actual continuous linear maps. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev FiniteLpSpace (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (N : ℕ) :=
  lp (fun _ : Fin N => 𝕜) p.val

abbrev FiniteMatrixBlock (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (N : ℕ) :=
  FiniteLpSpace 𝕜 p N →L[𝕜] FiniteLpSpace 𝕜 p N

/-- The actual rank-one unit e_ij, sending e_j to e_i. -/
def matrixUnit (p : BanachExponent) {N : ℕ} (i j : Fin N) : FiniteMatrixBlock 𝕜 p N :=
  (lpCoordinate p.val j).smulRight (lp.single p.val i (1 : 𝕜))

@[simp] theorem matrixUnit_apply (p : BanachExponent) {N : ℕ} (i j : Fin N)
    (x : FiniteLpSpace 𝕜 p N) (k : Fin N) :
    matrixUnit p i j x k = if k = i then x j else 0 := by
  simp [matrixUnit, lp.single_apply, Pi.single_apply]

theorem norm_matrixUnit (p : BanachExponent) {N : ℕ} (i j : Fin N) :
    ‖matrixUnit (𝕜 := 𝕜) p i j‖ = 1 := by
  have hu (k : Fin N) : ‖(lp.single p.val k (1 : 𝕜) : FiniteLpSpace 𝕜 p N)‖ = 1 := by
    rw [lp.norm_single (zero_lt_one.trans_le p.property), norm_one]
  apply le_antisymm
  · rw [matrixUnit, ContinuousLinearMap.norm_smulRight_apply, hu, mul_one]
    exact norm_lpCoordinate_le p.val j
  · have h := (matrixUnit (𝕜 := 𝕜) p i j).le_opNorm (lp.single p.val j (1 : 𝕜))
    have heq : matrixUnit p i j (lp.single p.val j (1 : 𝕜)) =
        (lp.single p.val i (1 : 𝕜) : FiniteLpSpace 𝕜 p N) := by
      simp [matrixUnit]
    simpa only [heq, hu, mul_one] using h

/-- The actual matrix-entry functional A ↦ (A e_j)_i. -/
def matrixEntry (p : BanachExponent) {N : ℕ} (i j : Fin N) :
    FiniteMatrixBlock 𝕜 p N →L[𝕜] 𝕜 :=
  (lpCoordinate p.val i).comp
    (ContinuousLinearMap.apply 𝕜 (FiniteLpSpace 𝕜 p N) (lp.single p.val j (1 : 𝕜)))

@[simp] theorem matrixEntry_apply (p : BanachExponent) {N : ℕ} (i j : Fin N)
    (A : FiniteMatrixBlock 𝕜 p N) :
    matrixEntry p i j A = A (lp.single p.val j (1 : 𝕜)) i := rfl

/-- Composition on both sides, as a bounded map between operator spaces. -/
def operatorSandwich {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (A : F →L[𝕜] H) (B : G →L[𝕜] E) : (E →L[𝕜] F) →L[𝕜] (G →L[𝕜] H) :=
  (ContinuousLinearMap.compL 𝕜 G F H A).comp ((ContinuousLinearMap.compL 𝕜 G E F).flip B)

@[simp] theorem operatorSandwich_apply {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (A : F →L[𝕜] H) (B : G →L[𝕜] E) (T : E →L[𝕜] F) :
    operatorSandwich A B T = (A.comp T).comp B := rfl

def matrixInsert (p : BanachExponent) {n N : ℕ} (α τ : Fin n ↪ Fin N) :
    FiniteMatrixBlock 𝕜 p n →L[𝕜] FiniteMatrixBlock 𝕜 p N :=
  operatorSandwich (lpExtend (𝕜 := 𝕜) (X := 𝕜) p.val α) (lpRestrict p.val τ)

def matrixRestrict (p : BanachExponent) {n N : ℕ} (α τ : Fin n ↪ Fin N) :
    FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p n :=
  operatorSandwich (lpRestrict (𝕜 := 𝕜) (X := 𝕜) p.val α) (lpExtend p.val τ)

def matrixBlockProjection (p : BanachExponent) {n N : ℕ} (α τ : Fin n ↪ Fin N) :
    FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N :=
  (matrixInsert p α τ).comp (matrixRestrict p α τ)

theorem matrixRestrict_comp_insert (p : BanachExponent) {n N : ℕ} (α τ : Fin n ↪ Fin N) :
    (matrixRestrict (𝕜 := 𝕜) p α τ).comp (matrixInsert p α τ) =
      ContinuousLinearMap.id 𝕜 (FiniteMatrixBlock 𝕜 p n) := by
  ext T x i
  change lpExtend (𝕜 := 𝕜) p.val α
    (T (lpRestrict (𝕜 := 𝕜) p.val τ (lpExtend p.val τ x))) (α i) = T x i
  rw [lpExtend_apply_image]
  exact congrArg (fun y => T y i)
    (DFunLike.congr_fun (lpRestrict_comp_extend (𝕜 := 𝕜) (X := 𝕜) (p := p.val) τ) x)

theorem norm_operatorSandwich_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (A : F →L[𝕜] H) (B : G →L[𝕜] E) : ‖operatorSandwich A B‖ ≤ ‖A‖ * ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro T
  rw [operatorSandwich_apply]
  calc
    _ ≤ (‖A‖ * ‖T‖) * ‖B‖ := ((A.comp T).opNorm_comp_le B).trans
      (mul_le_mul_of_nonneg_right (A.opNorm_comp_le T) (norm_nonneg _))
    _ = _ := by ring

theorem norm_matrixInsert_le (p : BanachExponent) {n N : ℕ} (α τ : Fin n ↪ Fin N) :
    ‖matrixInsert (𝕜 := 𝕜) p α τ‖ ≤ 1 := by
  apply (norm_operatorSandwich_le _ _).trans
  simpa only [mul_one] using mul_le_mul
    (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) α)
    (norm_lpRestrict_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) τ) (norm_nonneg _) zero_le_one

theorem norm_matrixRestrict_le (p : BanachExponent) {n N : ℕ} (α τ : Fin n ↪ Fin N) :
    ‖matrixRestrict (𝕜 := 𝕜) p α τ‖ ≤ 1 := by
  apply (norm_operatorSandwich_le _ _).trans
  simpa only [mul_one] using mul_le_mul
    (norm_lpRestrict_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) α)
    (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) τ) (norm_nonneg _) zero_le_one

theorem matrixBlockProjection_idempotent (p : BanachExponent) {n N : ℕ} (α τ : Fin n ↪ Fin N) :
    (matrixBlockProjection (𝕜 := 𝕜) p α τ).comp (matrixBlockProjection p α τ) =
      matrixBlockProjection p α τ := by
  simp only [matrixBlockProjection, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (matrixRestrict (𝕜 := 𝕜) p α τ),
    matrixRestrict_comp_insert, ContinuousLinearMap.id_comp]

/-- Auxiliary Hilbert–Schmidt norm; the space itself still has its original operator norm. -/
def matrixHilbertSchmidtNorm (p : BanachExponent) {N : ℕ} (A : FiniteMatrixBlock 𝕜 p N) : ℝ :=
  Real.sqrt (∑ i : Fin N, ∑ j : Fin N, ‖matrixEntry p i j A‖ ^ 2)

end ThesisCommon
