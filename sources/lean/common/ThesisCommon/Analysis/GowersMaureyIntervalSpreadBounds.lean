import ThesisCommon.Analysis.GowersMaureyAdjointSpreads
import ThesisCommon.Analysis.GowersMaureyIntervalNorms

/-! Tail spreads contract every actual finite-interval norm. Pulling back
the intervals preserves their order, including empty intervals and clipping
at the domain cutoff. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey

theorem Interval.spreadImage_mem_ge_target (E : Interval) (m n : ℕ)
    {i : ℕ} (hi : i ∈ (E.spreadImage m n).set) : n ≤ i := by
  unfold Interval.spreadImage at hi
  split_ifs at hi with h
  · simp only [Interval.set, Finset.mem_Icc] at hi
    omega
  · simp only [Interval.set, Finset.mem_Icc] at hi
    omega

theorem Interval.mem_spreadImage_target (E : Interval) (m n i : ℕ) (hi : n ≤ i) :
    i ∈ (E.spreadImage m n).set ↔ i - n + m ∈ E.set := by
  have hm : m ≤ i - n + m := by omega
  have heq : (i - n + m) - m + n = i := by omega
  simpa only [heq] using E.mem_spreadImage m n (i - n + m) hm

variable {𝕜 : Type*} [RCLike 𝕜]

theorem restrict_spread_pullback (E : Interval) (m n : ℕ) (x : C00 𝕜) :
    restrict E (spread m n x) = spread m n (restrict (E.spreadImage n m) x) := by
  ext i
  simp only [restrict_apply, spread_apply]
  by_cases hi : n ≤ i
  · simp only [hi, if_pos, E.mem_spreadImage n m i hi]
  · simp [hi]

def FiniteIntervalFamily.spreadPullback {N : ℕ} (I : FiniteIntervalFamily N)
    (m n : ℕ) : FiniteIntervalFamily N where
  interval i := (I.interval i).spreadImage n m
  successive := by
    intro i j hij s hs t ht
    have hsm := (I.interval i).spreadImage_mem_ge_target n m hs
    have htm := (I.interval j).spreadImage_mem_ge_target n m ht
    have hs' := ((I.interval i).mem_spreadImage_target n m s hsm).mp hs
    have ht' := ((I.interval j).mem_spreadImage_target n m t htm).mp ht
    have hlt := I.successive i j hij _ hs' _ ht'
    omega

theorem intervalNorm_spread_le (D : ConstructionData 𝕜) (N m n : ℕ)
    (x : C00 𝕜) : intervalNorm D N (spread m n x) ≤ intervalNorm D N x := by
  rw [intervalNorm, Seminorm.sSup_apply (intervalSums_bddAbove D N)]
  apply ciSup_le
  rintro ⟨_, I, rfl⟩
  change intervalSum D I (spread m n x) ≤ _
  apply le_trans _ (intervalSum_le_intervalNorm D (I.spreadPullback m n) x)
  change intervalSum D I (spread m n x) ≤ intervalSum D (I.spreadPullback m n) x
  rw [intervalSum_apply, intervalSum_apply]
  apply Finset.sum_le_sum
  intro i hi
  rw [restrict_spread_pullback]
  exact implicitNorm_spread_le D m n _

end ThesisCommon.GowersMaurey
