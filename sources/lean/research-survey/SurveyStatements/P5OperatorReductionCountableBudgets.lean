import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Positive tolerances for every member of a countable family. The actual
normalization factor can vary arbitrarily: the weighted total remains
summable and small. Finite selection uses only finitely many of these
already fixed positive tolerances. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace SurveyStatements.P5OperatorReduction

theorem exists_positive_countable_error_budget {I : Type*} [Countable I]
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : I → ℝ, (∀ i, 0 < b i) ∧ Summable b ∧
      Summable (fun i => C i * b i) ∧
      (∑' i, b i) ≤ ε / 2 ∧ (∑' i, C i * b i) ≤ ε / 2 := by
  letI : Encodable I := Encodable.ofCountable I
  let a (i : I) : ℝ := (ε / 4) * (1 / 2 : ℝ) ^ Encodable.encode i
  let b (i : I) : ℝ := a i / (C i + 1)
  have ha : Summable a := summable_geometric_two_encode.mul_left (ε / 4)
  have htotal : (∑' i : I, (1 / 2 : ℝ) ^ Encodable.encode i) ≤ 2 := by
    have h := Summable.tsum_le_tsum_of_inj (fun i : I => Encodable.encode i)
      Encodable.encode_injective
      (fun n _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)
      (fun _ => le_rfl) (summable_geometric_two_encode (ι := I)) summable_geometric_two
    simpa only [tsum_geometric_two] using h
  have hatotal : (∑' i, a i) ≤ ε / 2 := by
    dsimp only [a]
    rw [tsum_mul_left]
    nlinarith
  have hbpos (i : I) : 0 < b i := by
    have hCi := hC i
    dsimp only [b, a]
    positivity
  have hidentity (i : I) : (C i + 1) * b i = a i := by
    dsimp only [b]
    exact mul_div_cancel₀ (a i) (by linarith [hC i])
  have hb_le (i : I) : b i ≤ a i := by
    nlinarith [hidentity i, hC i, hbpos i]
  have hCb_le (i : I) : C i * b i ≤ a i := by
    nlinarith [hidentity i, hbpos i]
  have hb : Summable b := Summable.of_nonneg_of_le (fun i => (hbpos i).le) hb_le ha
  have hCb : Summable (fun i => C i * b i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hC i) (hbpos i).le) hCb_le ha
  exact ⟨b, hbpos, hb, hCb, (hb.tsum_le_tsum hb_le ha).trans hatotal,
    (hCb.tsum_le_tsum hCb_le ha).trans hatotal⟩

end SurveyStatements.P5OperatorReduction
