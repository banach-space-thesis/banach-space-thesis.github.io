import LindenstraussRetraction.CoordinateTruncation
import LindenstraussRetraction.Interlacing
import Lean.Elab.Tactic.Omega

/-! # Prefix averages in c₀ and the geometry of interlaced tuples -/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace LindenstraussRetraction

universe v
variable (𝕜 : Type v) [RCLike 𝕜]

/-- The finite prefix which is one on coordinates `0,...,n`. -/
def c0Prefix (n : ℕ) : C0 𝕜 where
  toFun j := if j ≤ n then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n+1)] with j hj
    have hnj : ¬ j ≤ n := by omega
    simp only [hnj, if_false]

@[simp] theorem c0Prefix_apply (n j : ℕ) :
    c0Prefix 𝕜 n j = if j ≤ n then 1 else 0 := rfl

theorem norm_c0Prefix_le_one (n : ℕ) : ‖c0Prefix 𝕜 n‖ ≤ 1 := by
  change ‖(c0Prefix 𝕜 n).toBCF‖ ≤ 1
  apply (BoundedContinuousFunction.norm_le zero_le_one).2
  intro j
  change ‖if j ≤ n then (1 : 𝕜) else 0‖ ≤ 1
  split_ifs <;> simp

/-- Coordinate evaluation with its inherited supremum-norm bound. -/
def c0Coordinate (j : ℕ) : C0 𝕜 →L[𝕜] 𝕜 :=
  ({ toFun x := x j
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : C0 𝕜 →ₗ[𝕜] 𝕜).mkContinuous 1 (fun x => by
       simpa only [one_mul] using x.toBCF.norm_coe_le_norm j)

@[simp] theorem c0Coordinate_apply (j : ℕ) (x : C0 𝕜) :
    c0Coordinate 𝕜 j x = x j := rfl

theorem norm_c0Coordinate_apply_le (j : ℕ) (x : C0 𝕜) :
    ‖c0Coordinate 𝕜 j x‖ ≤ ‖x‖ := x.toBCF.norm_coe_le_norm j

theorem norm_c0Coordinate_le_one (j : ℕ) : ‖c0Coordinate 𝕜 j‖ ≤ 1 := by
  apply (c0Coordinate 𝕜 j).opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using norm_c0Coordinate_apply_le 𝕜 j x

/-- The sum of the prefixes indexed by a finite tuple. -/
def prefixSum {k : ℕ} (a : Fin k → ℕ) : C0 𝕜 := ∑ i, c0Prefix 𝕜 (a i)

@[simp] theorem prefixSum_apply {k : ℕ} (a : Fin k → ℕ) (j : ℕ) :
    prefixSum 𝕜 a j = ∑ i, if j ≤ a i then (1 : 𝕜) else 0 := by
  change c0Coordinate 𝕜 j (∑ i, c0Prefix 𝕜 (a i)) = _
  rw [map_sum]
  rfl

theorem norm_prefixSum_le {k : ℕ} (a : Fin k → ℕ) :
    ‖prefixSum 𝕜 a‖ ≤ (k : ℝ) := by
  calc
    ‖prefixSum 𝕜 a‖ ≤ ∑ i, ‖c0Prefix 𝕜 (a i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun i _ => norm_c0Prefix_le_one 𝕜 (a i))
    _ = k := by simp

/-- The normalized sum `(1/k) Σ_i p_(a_i)`; it is zero when `k=0`. -/
def prefixAverage {k : ℕ} (a : Fin k → ℕ) : C0 𝕜 :=
  (k : 𝕜)⁻¹ • prefixSum 𝕜 a

@[simp] theorem prefixAverage_apply {k : ℕ} (a : Fin k → ℕ) (j : ℕ) :
    prefixAverage 𝕜 a j = (k : 𝕜)⁻¹ *
      ∑ i, if j ≤ a i then (1 : 𝕜) else 0 := by
  simp only [prefixAverage, ZeroAtInftyContinuousMap.smul_apply, prefixSum_apply, smul_eq_mul]

theorem norm_prefixAverage_le_one {k : ℕ} (a : Fin k → ℕ) :
    ‖prefixAverage 𝕜 a‖ ≤ 1 := by
  by_cases hk : k = 0
  · subst k
    simp [prefixAverage]
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  calc
    ‖prefixAverage 𝕜 a‖ = (k : ℝ)⁻¹ * ‖prefixSum 𝕜 a‖ := by
      rw [prefixAverage, norm_smul, norm_inv, RCLike.norm_natCast]
    _ ≤ (k : ℝ)⁻¹ * k :=
      mul_le_mul_of_nonneg_left (norm_prefixSum_le 𝕜 a) (inv_nonneg.mpr hk'.le)
    _ = 1 := inv_mul_cancel₀ hk'.ne'

theorem prefixAverage_apply_eq_one {k : ℕ} (hk : 0 < k)
    (a : Fin k → ℕ) (j : ℕ) (hja : ∀ i, j ≤ a i) :
    prefixAverage 𝕜 a j = 1 := by
  rw [prefixAverage_apply]
  simp only [if_pos (hja _), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))

def evenPosition {k : ℕ} (i : Fin k) : Fin (2*k) := ⟨2*i.val, by omega⟩
def oddPosition {k : ℕ} (i : Fin k) : Fin (2*k) := ⟨2*i.val+1, by omega⟩

private theorem prefix_sub_apply {a b : ℕ} (hab : a ≤ b) (j : ℕ) :
    c0Prefix 𝕜 a j - c0Prefix 𝕜 b j =
      if a < j ∧ j ≤ b then (-1 : 𝕜) else 0 := by
  by_cases hja : j ≤ a
  · have hjb : j ≤ b := hja.trans hab
    simp [hja, hjb, not_lt.mpr hja]
  · by_cases hjb : j ≤ b
    · simp [hja, hjb, lt_of_not_ge hja]
    · simp [hja, hjb]

/-- Consecutive disjoint intervals allow at most one prefix difference at each
coordinate, so the unnormalized alternating sum has norm at most one. -/
theorem norm_prefixSum_interlaced_sub_le_one {k : ℕ}
    (a : Fin (2*k) → ℕ) (ha : StrictMono a) :
    ‖prefixSum 𝕜 (evenCoordinates k a) - prefixSum 𝕜 (oddCoordinates k a)‖ ≤ 1 := by
  classical
  change ‖(prefixSum 𝕜 (evenCoordinates k a) - prefixSum 𝕜 (oddCoordinates k a)).toBCF‖ ≤ 1
  apply (BoundedContinuousFunction.norm_le zero_le_one).2
  intro j
  let active : Fin k → Prop := fun i => a (evenPosition i) < j ∧ j ≤ a (oddPosition i)
  have hcoord : (prefixSum 𝕜 (evenCoordinates k a) - prefixSum 𝕜 (oddCoordinates k a)) j =
      ∑ i : Fin k, if active i then (-1 : 𝕜) else 0 := by
    change c0Coordinate 𝕜 j (prefixSum 𝕜 (evenCoordinates k a) - prefixSum 𝕜 (oddCoordinates k a)) = _
    rw [map_sub, c0Coordinate_apply, c0Coordinate_apply, prefixSum_apply, prefixSum_apply,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply prefix_sub_apply 𝕜
    apply (ha _).le
    change 2*i.val < 2*i.val+1
    omega
  change ‖(prefixSum 𝕜 (evenCoordinates k a) - prefixSum 𝕜 (oddCoordinates k a)) j‖ ≤ 1
  rw [hcoord]
  by_cases hex : ∃ i, active i
  · obtain ⟨i, hi⟩ := hex
    have hunique : ∀ b : Fin k, b ≠ i → ¬ active b := by
      intro b hbi hb
      rcases lt_or_gt_of_ne hbi with hlt | hgt
      · have hp : oddPosition b < evenPosition i := by
          change 2*b.val+1 < 2*i.val
          change b.val < i.val at hlt
          omega
        have hh := ha hp
        dsimp [active] at hi hb
        omega
      · have hp : oddPosition i < evenPosition b := by
          change 2*i.val+1 < 2*b.val
          change i.val < b.val at hgt
          omega
        have hh := ha hp
        dsimp [active] at hi hb
        omega
    have hsum : (∑ b : Fin k, if active b then (-1 : 𝕜) else 0) = -1 := by
      rw [Finset.sum_eq_single i]
      · exact if_pos hi
      · intro b _ hbi
        exact if_neg (hunique b hbi)
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ i))
    rw [hsum]
    simp
  · have hn : ∀ i, ¬ active i := fun i hi => hex ⟨i, hi⟩
    simp only [if_neg (hn _), Finset.sum_const_zero, norm_zero]
    exact zero_le_one

/-- Adjacent interlaced tuple averages are within `1/k` in the c₀ norm. -/
theorem norm_prefixAverage_interlaced_sub_le {k : ℕ}
    (a : Fin (2*k) → ℕ) (ha : StrictMono a) :
    ‖prefixAverage 𝕜 (evenCoordinates k a) - prefixAverage 𝕜 (oddCoordinates k a)‖ ≤ 1 / (k : ℝ) := by
  rw [prefixAverage, prefixAverage, ← smul_sub, norm_smul, norm_inv, RCLike.norm_natCast]
  calc
    (k : ℝ)⁻¹ * ‖prefixSum 𝕜 (evenCoordinates k a) - prefixSum 𝕜 (oddCoordinates k a)‖ ≤
        (k : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left
      (norm_prefixSum_interlaced_sub_le_one 𝕜 a ha) (inv_nonneg.mpr (Nat.cast_nonneg k))
    _ = 1 / (k : ℝ) := by simp [one_div]

end LindenstraussRetraction
