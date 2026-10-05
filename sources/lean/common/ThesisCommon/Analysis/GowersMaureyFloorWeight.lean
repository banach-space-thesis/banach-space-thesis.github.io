import ThesisCommon.Analysis.GowersMaureyFactorCostBounds
import ThesisCommon.Analysis.GowersMaureyRapidProducts

/-! The logarithmic interval budget survives natural flooring of a square
root, with an explicit constant and the positive-size hypothesis retained. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem logarithmicWeight_le_four_floor_sqrt {N : ℝ} (hN : 1 ≤ N) :
    logarithmicWeight N ≤ 4 * logarithmicWeight (⌊Real.sqrt N⌋₊ : ℝ) := by
  have hs : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hfloor : (1 : ℝ) ≤ (⌊Real.sqrt N⌋₊ : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.floor_pos.mpr hs)
  have htwo : 1 ≤ 2 * (⌊Real.sqrt N⌋₊ : ℝ) := by linarith
  have hbound : Real.sqrt N ≤ 2 * (⌊Real.sqrt N⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.sqrt N)
    linarith
  have hmono : logarithmicWeight (Real.sqrt N) ≤
      logarithmicWeight (2 * (⌊Real.sqrt N⌋₊ : ℝ)) :=
    logarithmicWeight_strictMonoOn.monotoneOn hs htwo hbound
  have hmul := logarithmicWeight_submultiplicative
    (by norm_num : (1 : ℝ) ≤ 2) hfloor
  have hnonneg : 0 ≤ logarithmicWeight (⌊Real.sqrt N⌋₊ : ℝ) :=
    zero_le_one.trans (one_le_logarithmicWeight_real hfloor)
  have hcost : logarithmicWeight (2 : ℝ) ≤ 2 :=
    logarithmicWeight_le_self_real (by norm_num)
  calc
    logarithmicWeight N ≤ 2 * logarithmicWeight (Real.sqrt N) :=
      logarithmicWeight_le_twice_sqrt (zero_le_one.trans hN)
    _ ≤ 2 * logarithmicWeight (2 * (⌊Real.sqrt N⌋₊ : ℝ)) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ ≤ 2 * (logarithmicWeight 2 * logarithmicWeight (⌊Real.sqrt N⌋₊ : ℝ)) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ ≤ 4 * logarithmicWeight (⌊Real.sqrt N⌋₊ : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hcost hnonneg
      linarith

theorem ConstructionData.weight_le_four_floor_sqrt
    {𝕜 : Type*} [RCLike 𝕜] (D : ConstructionData 𝕜) (n : ℕ) :
    logarithmicWeight (D.j n) ≤
      4 * logarithmicWeight (⌊Real.sqrt (D.j n : ℝ)⌋₊ : ℝ) :=
  logarithmicWeight_le_four_floor_sqrt (D.one_le_size n)

end ThesisCommon.GowersMaurey
