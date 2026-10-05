import ThesisCommon.Analysis.LebesgueLpPartition
import Mathlib.Analysis.SpecificLimits.Basic

/-! The dyadic measurable partition of `[0,1]` used to prove `Lp` self-similarity. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Function
namespace ThesisCommon

def intervalLpDyadicRadius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
def intervalLpDyadicBlock (n : ℕ) : Set ℝ :=
  Ioc (intervalLpDyadicRadius (n + 1)) (intervalLpDyadicRadius n)

theorem intervalLpDyadicRadius_pos (n : ℕ) : 0 < intervalLpDyadicRadius n := by
  exact pow_pos (by norm_num) n

theorem intervalLpDyadicRadius_antitone : Antitone intervalLpDyadicRadius := by
  intro m n hmn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn

theorem intervalLpDyadicBlock_subset (n : ℕ) : intervalLpDyadicBlock n ⊆ Icc 0 1 := by
  intro x hx
  exact ⟨(intervalLpDyadicRadius_pos (n + 1)).le.trans hx.1.le,
    hx.2.trans (by simpa [intervalLpDyadicRadius] using intervalLpDyadicRadius_antitone (Nat.zero_le n))⟩

theorem intervalLpDyadicBlock_disjoint : Pairwise (Disjoint on intervalLpDyadicBlock) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hmn with h | h
  · have := intervalLpDyadicRadius_antitone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hy.2.trans this)) hx.1
  · have := intervalLpDyadicRadius_antitone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hx.2.trans this)) hy.1

theorem intervalLpDyadicBlock_union : (⋃ n, intervalLpDyadicBlock n) = Ioc 0 1 := by
  ext x
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact ⟨(intervalLpDyadicRadius_pos (n + 1)).trans hn.1,
      (intervalLpDyadicBlock_subset n hn).2⟩
  · intro hx
    have hex : ∃ n : ℕ, intervalLpDyadicRadius n < x :=
      exists_pow_lt_of_lt_one hx.1 (by norm_num)
    let N := Nat.find hex
    have hN : intervalLpDyadicRadius N < x := Nat.find_spec hex
    have hN0 : N ≠ 0 := by
      intro h
      rw [h] at hN
      exact (not_lt_of_ge hx.2) (by simpa [intervalLpDyadicRadius] using hN)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · simpa [hn] using hN
    · exact le_of_not_gt (Nat.find_min hex (by omega : n < Nat.find hex))

theorem intervalLpDyadicBlock_cover :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ ⋃ n, intervalLpDyadicBlock n := by
  rw [intervalLpDyadicBlock_union]
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℝ)))] with x hx hzero
  exact ⟨lt_of_le_of_ne hx.1 (by simpa [eq_comm] using hzero), hx.2⟩

/-- The dyadic partition gives an exact isometry onto the `lp` sum of its
restricted-measure block spaces.  Affine rescaling will identify these blocks. -/
def intervalLpFunctionPartition (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) :
    IntervalLp 𝕜 p ≃ₗᵢ[𝕜]
      lp (fun n : ℕ => Lp 𝕜 p.val
        ((volume.restrict (Icc (0 : ℝ) 1)).restrict (intervalLpDyadicBlock n))) p.val :=
  lebesgueLpPartitionEquiv hp intervalLpDyadicBlock (fun _ => measurableSet_Ioc)
    intervalLpDyadicBlock_disjoint intervalLpDyadicBlock_cover

end ThesisCommon
