import ThesisCommon.Analysis.UncountableSchauderDiagonalSelection
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-! A genuine bounded rank-one operator on any real countable normalized
unconditional sum whose every coordinate matrix entry is nonzero. Both
its vector and functional are norm-convergent geometric series. -/
noncomputable section
open scoped BigOperators Cardinal
namespace ThesisCommon.UncountableSchauderSum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (b : NormalizedSchauderFamily ℝ ℕ E) (hb : b.IsOneUnconditional)

def geometricFullVector : UncountableSchauderSum b hb ℝ :=
  ∑' n : ℕ, (1/2 : ℝ)^n • single n (1 : ℝ)

theorem summable_geometric_single :
    Summable (fun n : ℕ => (1/2 : ℝ)^n • (single (b := b) (hb := hb) n (1 : ℝ))) := by
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).of_norm_bounded
  intro n
  simp only [norm_smul,norm_single,norm_one,mul_one,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n)]
  exact le_rfl

theorem geometricFullVector_apply (n : ℕ) : geometricFullVector b hb n = (1/2 : ℝ)^n := by
  change coordinate (b := b) (hb := hb) (Y := ℝ) n
    (∑' i : ℕ, (1/2 : ℝ)^i • (single (b := b) (hb := hb) i (1 : ℝ))) = _
  rw [(coordinate (b := b) (hb := hb) (Y := ℝ) n).map_tsum (summable_geometric_single b hb)]
  simp only [map_smul,coordinate_apply,single_apply,smul_eq_mul]
  rw [tsum_eq_single n]
  · simp
  · intro i hi
    simp [Ne.symm hi]

theorem geometricFullVector_ne_zero : geometricFullVector b hb ≠ 0 := by
  intro h
  have hh := geometricFullVector_apply b hb 0
  rw [h] at hh
  norm_num at hh

def geometricFullFunctional : UncountableSchauderSum b hb ℝ →L[ℝ] ℝ :=
  ∑' n : ℕ, (1/2 : ℝ)^n • coordinate n

theorem summable_geometric_coordinate :
    Summable (fun n : ℕ => (1/2 : ℝ)^n •
      (coordinate (b := b) (hb := hb) (Y := ℝ) n)) := by
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n)]
  exact (mul_le_mul_of_nonneg_left (norm_coordinate_le n) (by positivity)).trans_eq (mul_one _)

theorem geometricFullFunctional_single (n : ℕ) :
    geometricFullFunctional b hb (single n (1 : ℝ)) = (1/2 : ℝ)^n := by
  change (ContinuousLinearMap.apply ℝ ℝ (single n (1 : ℝ)))
    (∑' i : ℕ, (1/2 : ℝ)^i • (coordinate (b := b) (hb := hb) (Y := ℝ) i)) = _
  rw [(ContinuousLinearMap.apply ℝ ℝ _).map_tsum (summable_geometric_coordinate b hb)]
  simp only [ContinuousLinearMap.apply_apply,ContinuousLinearMap.smul_apply,
    coordinate_apply,single_apply,smul_eq_mul]
  rw [tsum_eq_single n]
  · simp
  · intro i hi
    simp [hi]

def geometricRankOne : UncountableSchauderSum b hb ℝ →L[ℝ] UncountableSchauderSum b hb ℝ :=
  (geometricFullFunctional b hb).smulRight (geometricFullVector b hb)

theorem geometricRankOne_range :
    LinearMap.range (geometricRankOne b hb).toLinearMap =
      Submodule.span ℝ {geometricFullVector b hb} := by
  apply ContinuousLinearMap.range_smulRight_apply
  intro h
  have hh := geometricFullFunctional_single b hb 0
  rw [h] at hh
  norm_num at hh

theorem geometricRankOne_rank_one :
    Module.finrank ℝ (LinearMap.range (geometricRankOne b hb).toLinearMap) = 1 := by
  rw [geometricRankOne_range]
  exact finrank_span_singleton (geometricFullVector_ne_zero b hb)

theorem geometricRankOne_entry_apply (β α : ℕ) :
    (coordinateEntry (geometricRankOne b hb) β α (single α (1 : ℝ))) β =
      (1/2 : ℝ)^α * (1/2 : ℝ)^β := by
  rw [coordinateEntry_apply]
  simp only [single_apply,ite_true,geometricRankOne,ContinuousLinearMap.smulRight_apply,
    smul_apply,smul_eq_mul,geometricFullFunctional_single,geometricFullVector_apply]

theorem geometricRankOne_entry_ne_zero (β α : ℕ) :
    coordinateEntry (geometricRankOne b hb) β α ≠ 0 := by
  intro h
  have hh := geometricRankOne_entry_apply b hb β α
  rw [h] at hh
  simp only [ContinuousLinearMap.zero_apply,zero_apply] at hh
  have hp : 0 < (1/2 : ℝ)^α * (1/2 : ℝ)^β := by positivity
  linarith

theorem no_full_cardinal_diagonal_for_geometricRankOne :
    ¬ ∃ Λ : Set ℕ, Cardinal.mk Λ = Cardinal.mk ℕ ∧
      ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β → coordinateEntry (geometricRankOne b hb) β α = 0 := by
  rintro ⟨Λ,hcard,hdiag⟩
  have hs : Λ.Subsingleton := by
    intro α hα β hβ
    by_contra hne
    exact geometricRankOne_entry_ne_zero b hb β α (hdiag α hα β hβ hne)
  have hc := hs.cardinalMk_le_one
  rw [hcard,Cardinal.mk_nat] at hc
  exact (not_le_of_gt Cardinal.one_lt_aleph0) hc

end ThesisCommon.UncountableSchauderSum
