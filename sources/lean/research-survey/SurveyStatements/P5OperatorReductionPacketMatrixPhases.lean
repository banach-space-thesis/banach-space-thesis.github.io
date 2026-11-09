import SurveyStatements.P5Support.LpHaarDiagonalBounds
import Mathlib.Data.Finset.Sort

/-! Norming phases and the actual normalized same-level operator matrix.
Every matrix entry is a genuine Haar coordinate of an actual bounded operator. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical ENNReal

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def packetMatrixNormingPhase (z : 𝕜) : 𝕜 := (‖z‖ : 𝕜) / z

theorem packetMatrixNormingPhase_norm_le (z : 𝕜) :
    ‖packetMatrixNormingPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [packetMatrixNormingPhase, hz]
  · rw [packetMatrixNormingPhase, norm_div, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)]

theorem packetMatrixNormingPhase_mul (z : 𝕜) :
    packetMatrixNormingPhase z * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [packetMatrixNormingPhase, hz]
  · exact div_mul_cancel₀ _ hz

theorem packetMatrixNormingPhase_sum_norm {ι : Type*}
    (S : Finset ι) (a : ι → 𝕜) :
    ‖∑ i ∈ S, packetMatrixNormingPhase (a i) * a i‖ = ∑ i ∈ S, ‖a i‖ := by
  simp_rw [packetMatrixNormingPhase_mul]
  rw [← RCLike.ofReal_sum, RCLike.norm_ofReal,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]

def operatorReductionPacketMatrix (p : BanachExponent)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (i j : Fin S.card) : 𝕜 :=
  lpHaarNormalizedCoordinate 𝕜 p (some ⟨n, S.orderEmbOfFin rfl i⟩)
    (Q (lpHaarNormalizedVector 𝕜 p (some ⟨n, S.orderEmbOfFin rfl j⟩)))

theorem packetMatrix_sum_index {α : Type*} [AddCommMonoid α] (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (g : Fin (2 ^ n) → α) :
    (∑ i : Fin S.card, g (S.orderEmbOfFin rfl i)) = ∑ k ∈ S, g k := by
  calc
    _ = ∑ k ∈ (Finset.univ : Finset (Fin S.card)).image (S.orderEmbOfFin rfl), g k :=
      (Finset.sum_image (f := g) (s := (Finset.univ : Finset (Fin S.card)))
        (g := S.orderEmbOfFin rfl)
        (fun i _ j _ hij => (S.orderEmbOfFin rfl).injective hij)).symm
    _ = _ := by rw [Finset.image_orderEmbOfFin_univ]

theorem packetMatrix_normalizedCoordinate_norm_le
    (p : BanachExponent) (hp : p.val ≠ ∞) (i : Option LpHaarTreeIndex) :
    ‖lpHaarNormalizedCoordinate 𝕜 p i‖ ≤ 6 := by
  have he : lpHaarIndexEquiv (lpHaarEncode i) = i := lpHaarDecode_encode i
  simpa only [intervalLpHaarBasis, he] using
    intervalLpHaarBasis_coord_norm_le 𝕜 p hp (lpHaarEncode i)

theorem packetMatrix_normalizedEntry_norm_le
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (i j : Option LpHaarTreeIndex) :
    ‖lpHaarNormalizedCoordinate 𝕜 p i (Q (lpHaarNormalizedVector 𝕜 p j))‖ ≤ 6 * ‖Q‖ := by
  calc
    _ ≤ ‖lpHaarNormalizedCoordinate 𝕜 p i‖ * ‖Q (lpHaarNormalizedVector 𝕜 p j)‖ :=
      (lpHaarNormalizedCoordinate 𝕜 p i).le_opNorm _
    _ ≤ 6 * (‖Q‖ * ‖lpHaarNormalizedVector 𝕜 p j‖) :=
      mul_le_mul (packetMatrix_normalizedCoordinate_norm_le p hp i) (Q.le_opNorm _)
        (norm_nonneg _) (by norm_num)
    _ = _ := by rw [lpHaarNormalizedVector_norm 𝕜 p hp, mul_one]

theorem operatorReductionPacketMatrix_entry_norm_le
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (i j : Fin S.card) :
    ‖operatorReductionPacketMatrix p Q n S i j‖ ≤ 6 * ‖Q‖ :=
  packetMatrix_normalizedEntry_norm_le p hp Q _ _

end SurveyStatements.P5OperatorReduction
