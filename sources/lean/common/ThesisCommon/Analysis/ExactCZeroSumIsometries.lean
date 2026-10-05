import ThesisCommon.Analysis.ExactSequenceSumIsometries

/-! The norm-exact null-sequence identifications used by Appendix A. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem equivNormBound_cZeroProd_one :
    EquivNormBound (cZeroProdEquiv (𝕜 := 𝕜) (ι := ℕ) (X := X) (Y := Y)) 1 := by
  constructor
  · intro x
    apply max_le
    · exact cZero_norm_le_mul_of_pointwise x _ zero_le_one
        (fun i => by simpa using norm_fst_le (x i))
    · exact cZero_norm_le_mul_of_pointwise x _ zero_le_one
        (fun i => by simpa using norm_snd_le (x i))
  · intro x
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
    intro i
    change ‖(x.1 i, (0 : Y)) + ((0 : X), x.2 i)‖ ≤ ‖x‖
    simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.norm_def]
    exact max_le
      ((BoundedContinuousFunction.norm_coe_le_norm x.1.toBCF i).trans (norm_fst_le x))
      ((BoundedContinuousFunction.norm_coe_le_norm x.2.toBCF i).trans (norm_snd_le x))

def cZeroProdIsometry : CZeroSum (X × Y) ≃ₗᵢ[𝕜] CZeroSum X × CZeroSum Y :=
  isometryEquivOfNormBoundOne cZeroProdEquiv equivNormBound_cZeroProd_one

theorem cZeroHeadTailEquiv_norm (x : CZeroSum X) :
    ‖cZeroHeadTailEquiv (𝕜 := 𝕜) x‖ = ‖x‖ := by
  let y := cZeroHeadTailEquiv (𝕜 := 𝕜) x
  apply le_antisymm
  · change max ‖x 0‖ ‖y.2‖ ≤ ‖x‖
    apply max_le
    · exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF 0
    · exact norm_cZeroRead_le sequenceSuccessor x
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg y)).mpr
    intro n
    cases n with
    | zero => exact le_max_left _ _
    | succ n => exact (BoundedContinuousFunction.norm_coe_le_norm y.2.toBCF n).trans (le_max_right _ _)

def cZeroHeadTailIsometry : CZeroSum X ≃ₗᵢ[𝕜] X × CZeroSum X :=
  ⟨cZeroHeadTailEquiv.toLinearEquiv, cZeroHeadTailEquiv_norm⟩

def cZeroMapIsometry (e : X ≃ₗᵢ[𝕜] Y) : CZeroSum X ≃ₗᵢ[𝕜] CZeroSum Y :=
  isometryEquivOfNormBoundOne (cZeroMapEquiv e.toContinuousLinearEquiv)
    ((equivNormBound_isometry e).cZeroMap zero_le_one)

def cZeroBanachProdIsometry :
    CZeroSum (BanachDirectSum ⟨∞, le_top⟩ X Y) ≃ₗᵢ[𝕜]
      BanachDirectSum ⟨∞, le_top⟩ (CZeroSum X) (CZeroSum Y) :=
  ((cZeroMapIsometry (WithLp.prodEquivₗᵢ (p := ∞) (𝕜 := 𝕜) (α := X) (β := Y))).trans
    (cZeroProdIsometry (𝕜 := 𝕜) (X := X) (Y := Y))).trans
    (WithLp.prodEquivₗᵢ (p := ∞) (𝕜 := 𝕜) (α := CZeroSum X) (β := CZeroSum Y)).symm

def cZeroBanachHeadTailIsometry :
    CZeroSum X ≃ₗᵢ[𝕜] BanachDirectSum ⟨∞, le_top⟩ X (CZeroSum X) :=
  (cZeroHeadTailIsometry (𝕜 := 𝕜) (X := X)).trans
    (WithLp.prodEquivₗᵢ (p := ∞) (𝕜 := 𝕜) (α := X) (β := CZeroSum X)).symm

end ThesisCommon

