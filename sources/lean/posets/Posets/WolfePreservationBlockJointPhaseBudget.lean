import Posets.WolfePreservationBlockJointPhaseRelation

/-! A quantitative section-mass budget. The three losses are the bad-row
variation, the small row totals, and the small normalized diagonal atoms. -/

noncomputable section
open scoped Classical
open Set Topology
namespace Posets

theorem wolfe_weighted_section_budget {I : Type*} (a b t l : I → ℝ)
    (Z : Set I) (ha : ∀ i, 0 ≤ a i) (ht : ∀ i, 0 ≤ t i)
    (hl : ∀ i, 0 ≤ l i) (htb : ∀ i, t i ≤ b i) (hlb : ∀ i, l i ≤ b i)
    (haSum : Summable a) (habSum : Summable (fun i => a i * b i))
    {c κ δ : ℝ} (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (hselect : ∀ i, b i ≤ c * t i → κ ≤ t i → δ * t i ≤ l i → i ∈ Z) :
    (∑' i, a i * l i) ≤ c * (∑' i, if i ∈ Z then a i * t i else 0) +
      (∑' i, if c * t i < b i then a i * b i else 0) +
        c * κ * (∑' i, a i) + δ * (∑' i, a i * t i) := by
  classical
  have hb (i : I) : 0 ≤ b i := (ht i).trans (htb i)
  have hat : Summable (fun i => a i * t i) := habSum.of_nonneg_of_le
    (fun i => mul_nonneg (ha i) (ht i)) (fun i => mul_le_mul_of_nonneg_left (htb i) (ha i))
  have hal : Summable (fun i => a i * l i) := habSum.of_nonneg_of_le
    (fun i => mul_nonneg (ha i) (hl i)) (fun i => mul_le_mul_of_nonneg_left (hlb i) (ha i))
  have hz : Summable (fun i => if i ∈ Z then a i * t i else 0) := by
    apply hat.of_nonneg_of_le
    · intro i; split_ifs; exact mul_nonneg (ha i) (ht i); exact le_rfl
    · intro i; split_ifs; exact le_rfl; exact mul_nonneg (ha i) (ht i)
  have hd : Summable (fun i => if c * t i < b i then a i * b i else 0) := by
    apply habSum.of_nonneg_of_le
    · intro i; split_ifs; exact mul_nonneg (ha i) (hb i); exact le_rfl
    · intro i; split_ifs; exact le_rfl; exact mul_nonneg (ha i) (hb i)
  have hp (i : I) : a i * l i ≤
      c * (if i ∈ Z then a i * t i else 0) +
      (if c * t i < b i then a i * b i else 0) +
        c * κ * a i + δ * (a i * t i) := by
    have hz0 : 0 ≤ c * (if i ∈ Z then a i * t i else 0) := by
      split_ifs
      · exact mul_nonneg hc (mul_nonneg (ha i) (ht i))
      · simp only [mul_zero, le_refl]
    have hk0 : 0 ≤ c * κ * a i := mul_nonneg (mul_nonneg hc hκ) (ha i)
    have hδ0 : 0 ≤ δ * (a i * t i) := mul_nonneg hδ (mul_nonneg (ha i) (ht i))
    by_cases hbad : c * t i < b i
    · rw [if_pos hbad]
      have hbnd := mul_le_mul_of_nonneg_left (hlb i) (ha i)
      linarith
    rw [if_neg hbad]
    have hgood := le_of_not_gt hbad
    by_cases hlarge : κ ≤ t i
    · by_cases hZ : i ∈ Z
      · rw [if_pos hZ]
        have hbnd := mul_le_mul_of_nonneg_left ((hlb i).trans hgood) (ha i)
        nlinarith
      · rw [if_neg hZ]
        have hsmall : l i < δ * t i := lt_of_not_ge (fun hh => hZ (hselect i hgood hlarge hh))
        have hbnd := mul_le_mul_of_nonneg_left hsmall.le (ha i)
        nlinarith
    · have hsmall := le_of_lt (lt_of_not_ge hlarge)
      have hbnd := mul_le_mul_of_nonneg_left
        ((hlb i).trans (hgood.trans (mul_le_mul_of_nonneg_left hsmall hc))) (ha i)
      linarith
  have hright := (((hz.mul_left c).add hd).add (haSum.mul_left (c * κ))).add (hat.mul_left δ)
  have hle := hal.tsum_le_tsum hp hright
  have he := (((hz.hasSum.mul_left c).add hd.hasSum).add
    (haSum.hasSum.mul_left (c * κ))).add (hat.hasSum.mul_left δ)
  rw [he.tsum_eq] at hle
  exact hle

end Posets
