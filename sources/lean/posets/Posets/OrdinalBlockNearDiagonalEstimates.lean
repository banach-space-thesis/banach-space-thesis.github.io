import JLMS.CZeroSumOperators
import JLMS.CZeroSumFinite
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Operator.Mul

/-! Near-diagonal estimates on arbitrary c₀ sums of compact C(Lᵢ) spaces.
The hypothesis concerns the norm of the entire evaluation row, including all
other blocks. No continuity is imposed on the scalar comparison functions. -/

noncomputable section
open Set Topology
namespace Posets
universe u v w
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {L : I → Type v}
  [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]

abbrev OrdinalBlockFunctionSum (𝕜 : Type w) [RCLike 𝕜] {I : Type u} (L : I → Type v)
    [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)] :=
  JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜))

local instance ordinalBlockNearDiagonalCoordinateGroup (i : I) : NormedAddCommGroup C(L i, 𝕜) :=
  inferInstance
local instance ordinalBlockNearDiagonalCoordinateSpace (i : I) : NormedSpace 𝕜 C(L i, 𝕜) :=
  inferInstance
local instance ordinalBlockNearDiagonalGroup : NormedAddCommGroup (OrdinalBlockFunctionSum 𝕜 L) :=
  inferInstance
local instance ordinalBlockNearDiagonalSpace : NormedSpace 𝕜 (OrdinalBlockFunctionSum 𝕜 L) :=
  inferInstance

def ordinalBlockEvaluation (i : I) (x : L i) : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] 𝕜 :=
  (ContinuousMap.evalCLM 𝕜 x).comp (JLMS.CZeroSum.evalCLM i)

@[simp] theorem ordinalBlockEvaluation_apply (i : I) (x : L i)
    (f : OrdinalBlockFunctionSum 𝕜 L) : ordinalBlockEvaluation i x f = f i x := rfl

def ordinalBlockDiagonal
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L) (i : I) : C(L i, 𝕜) :=
  A (JLMS.CZeroSum.single i 1) i

theorem ordinalBlock_one_norm_le (i : I) : ‖(1 : C(L i, 𝕜))‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro x
  simp

theorem ordinalBlockDiagonal_norm_le
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L) (i : I) :
    ‖ordinalBlockDiagonal A i‖ ≤ ‖A‖ := by
  let g : OrdinalBlockFunctionSum 𝕜 L := JLMS.CZeroSum.single i 1
  have hg : ‖g‖ ≤ 1 := by
    simpa only [g, JLMS.CZeroSum.norm_single] using
      ordinalBlock_one_norm_le (𝕜 := 𝕜) (L := L) i
  calc
    _ ≤ ‖A g‖ :=
      JLMS.CZeroSum.norm_apply_le_norm _ i
    _ ≤ ‖A‖ * ‖g‖ := A.le_opNorm g
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hg (norm_nonneg A)
    _ = ‖A‖ := mul_one _

theorem ordinalBlock_row_error_apply
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L)
    (a : ∀ i, L i → 𝕜) {ε : ℝ}
    (hrow : ∀ i x, ‖(ordinalBlockEvaluation i x).comp A -
      a i x • ordinalBlockEvaluation i x‖ ≤ ε)
    (f : OrdinalBlockFunctionSum 𝕜 L) (i : I) (x : L i) :
    ‖A f i x - a i x * f i x‖ ≤ ε * ‖f‖ := by
  have h := ((ordinalBlockEvaluation i x).comp A -
    a i x • ordinalBlockEvaluation i x).le_opNorm f
  exact h.trans (mul_le_mul_of_nonneg_right (hrow i x) (norm_nonneg f))

theorem ordinalBlockDiagonal_sub_scalar_le
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L)
    (a : ∀ i, L i → 𝕜) {ε : ℝ} (hε : 0 ≤ ε)
    (hrow : ∀ i x, ‖(ordinalBlockEvaluation i x).comp A -
      a i x • ordinalBlockEvaluation i x‖ ≤ ε) (i : I) (x : L i) :
    ‖ordinalBlockDiagonal A i x - a i x‖ ≤ ε := by
  have h := ordinalBlock_row_error_apply A a hrow (JLMS.CZeroSum.single i 1) i x
  simp only [JLMS.CZeroSum.single_apply_self, ContinuousMap.one_apply, mul_one,
    JLMS.CZeroSum.norm_single] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (ordinalBlock_one_norm_le i) hε).trans_eq (mul_one ε))

theorem ordinalBlockDiagonal_lower
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L)
    (a : ∀ i, L i → 𝕜) {d ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i x, d ≤ ‖a i x‖)
    (hrow : ∀ i x, ‖(ordinalBlockEvaluation i x).comp A -
      a i x • ordinalBlockEvaluation i x‖ ≤ ε) (i : I) (x : L i) :
    d - ε ≤ ‖ordinalBlockDiagonal A i x‖ := by
  have he := ordinalBlockDiagonal_sub_scalar_le A a hε hrow i x
  have hn := norm_sub_norm_le (a i x) (ordinalBlockDiagonal A i x)
  rw [norm_sub_rev] at hn
  linarith [hdiag i x]

theorem ordinalBlock_multiplier_norm_le (i : I) (b : C(L i, 𝕜)) :
    ‖ContinuousLinearMap.mul 𝕜 C(L i, 𝕜) b‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b)
  intro f
  exact norm_mul_le b f

def ordinalBlockDiagonalOperator
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L) :
    OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L :=
  JLMS.CZeroSum.mapCLM
    (fun i => ContinuousLinearMap.mul 𝕜 C(L i, 𝕜) (ordinalBlockDiagonal A i))
    (norm_nonneg A) (fun i => (ordinalBlock_multiplier_norm_le i _).trans
      (ordinalBlockDiagonal_norm_le A i))

@[simp] theorem ordinalBlockDiagonalOperator_apply
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L)
    (f : OrdinalBlockFunctionSum 𝕜 L) (i : I) (x : L i) :
    ordinalBlockDiagonalOperator A f i x = ordinalBlockDiagonal A i x * f i x := rfl

theorem ordinalBlockDiagonalOperator_error
    (A : OrdinalBlockFunctionSum 𝕜 L →L[𝕜] OrdinalBlockFunctionSum 𝕜 L)
    (a : ∀ i, L i → 𝕜) {ε : ℝ} (hε : 0 ≤ ε)
    (hrow : ∀ i x, ‖(ordinalBlockEvaluation i x).comp A -
      a i x • ordinalBlockEvaluation i x‖ ≤ ε) :
    ‖A - ordinalBlockDiagonalOperator A‖ ≤ 2 * ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply JLMS.CZeroSum.norm_le (by positivity)
  intro i
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖A f i x - ordinalBlockDiagonal A i x * f i x‖ ≤ _
  have he := ordinalBlock_row_error_apply A a hrow f i x
  have hb := ordinalBlockDiagonal_sub_scalar_le A a hε hrow i x
  have hx : ‖f i x‖ ≤ ‖f‖ := (f i).norm_coe_le_norm x |>.trans (f.norm_apply_le_norm i)
  have hsecond : ‖(a i x - ordinalBlockDiagonal A i x) * f i x‖ ≤ ε * ‖f‖ := by
    rw [norm_mul, norm_sub_rev]
    exact mul_le_mul hb hx (norm_nonneg _) hε
  have hid : A f i x - ordinalBlockDiagonal A i x * f i x =
      (A f i x - a i x * f i x) + (a i x - ordinalBlockDiagonal A i x) * f i x := by ring
  rw [hid]
  have hn := norm_add_le (A f i x - a i x * f i x)
    ((a i x - ordinalBlockDiagonal A i x) * f i x)
  nlinarith

end Posets
