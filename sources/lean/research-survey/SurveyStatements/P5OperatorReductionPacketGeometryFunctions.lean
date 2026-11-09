import SurveyStatements.P5RademacherPointwise
import SurveyStatements.P5Support.LpHaarBiorthogonal
import SurveyStatements.P5Support.LpHaarDyadicRefinement

/-! Actual finite same-level Haar packets with arbitrary bounded phase coefficients.
Disjoint parent cells leave at most one nonzero summand at each point. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def operatorReductionRawPacketFunction (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (a : Fin (2 ^ n) → 𝕜) (x : ℝ) : 𝕜 :=
  ∑ k ∈ S, a k * lpHaarFunction 𝕜
    (lpHaarCell (n + 1) (2 * k.val)) (lpHaarCell (n + 1) (2 * k.val + 1)) x

theorem operatorReductionRawPacketFunction_single (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (k : Fin (2 ^ n)) (hk : k ∈ S) {x : ℝ} (hx : x ∈ lpHaarCell n k) :
    operatorReductionRawPacketFunction n S a x = a k * lpHaarFunction 𝕜
      (lpHaarCell (n + 1) (2 * k.val)) (lpHaarCell (n + 1) (2 * k.val + 1)) x := by
  unfold operatorReductionRawPacketFunction
  apply Finset.sum_eq_single k
  · intro j _ hj
    have hparent : x ∉ lpHaarCell n j :=
      (lpHaarCell_disjoint_sameLevel n (fun h => hj (Fin.ext h))).notMem_of_mem_right hx
    have hchildren : x ∉ lpHaarCell (n + 1) (2 * j.val) ∪
        lpHaarCell (n + 1) (2 * j.val + 1) := by
      rw [lpHaarCell_children]
      exact hparent
    simp only [mem_union, not_or] at hchildren
    simp [lpHaarFunction, hchildren.1, hchildren.2]
  · intro hn
    exact (hn hk).elim

theorem operatorReductionRawPacketFunction_zero_off (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜) {x : ℝ}
    (hx : x ∉ lpHaarBlockParent n S) : operatorReductionRawPacketFunction n S a x = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hparent : x ∉ lpHaarCell n k := by
    intro h
    exact hx (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, h⟩⟩)
  have hchildren : x ∉ lpHaarCell (n + 1) (2 * k.val) ∪
      lpHaarCell (n + 1) (2 * k.val + 1) := by
    rw [lpHaarCell_children]
    exact hparent
  simp only [mem_union, not_or] at hchildren
  simp [lpHaarFunction, hchildren.1, hchildren.2]

theorem norm_operatorReductionRawPacketFunction_le (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ ≤ 1) (x : ℝ) :
    ‖operatorReductionRawPacketFunction n S a x‖ ≤
      (lpHaarBlockParent n S).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ lpHaarBlockParent n S
  · have hxe := hx
    simp only [lpHaarBlockParent, mem_iUnion] at hxe
    obtain ⟨k, hk, hxk⟩ := hxe
    rw [Set.indicator_of_mem hx, operatorReductionRawPacketFunction_single n S a k hk hxk,
      norm_mul, lpHaarFunction_norm _ _ (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)),
      lpHaarCell_children, Set.indicator_of_mem hxk, norm_one, mul_one]
    exact ha k hk
  · simpa only [Set.indicator_of_notMem hx,
      operatorReductionRawPacketFunction_zero_off n S a hx, norm_zero] using
      (le_rfl : (0 : ℝ) ≤ 0)

theorem norm_operatorReductionRawPacketFunction_eq (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ = 1) (x : ℝ) :
    ‖operatorReductionRawPacketFunction n S a x‖ =
      (lpHaarBlockParent n S).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ lpHaarBlockParent n S
  · have hxe := hx
    simp only [lpHaarBlockParent, mem_iUnion] at hxe
    obtain ⟨k, hk, hxk⟩ := hxe
    rw [Set.indicator_of_mem hx, operatorReductionRawPacketFunction_single n S a k hk hxk,
      norm_mul, lpHaarFunction_norm _ _ (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)),
      lpHaarCell_children, Set.indicator_of_mem hxk, norm_one, mul_one, ha k hk]
  · rw [Set.indicator_of_notMem hx, operatorReductionRawPacketFunction_zero_off n S a hx,
      norm_zero]

def operatorReductionRawHaarPacket (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜) : IntervalLp 𝕜 p :=
  ∑ k ∈ S, a k • lpHaarDyadic 𝕜 p n k

def operatorReductionNormalizedHaarPacket (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜) : IntervalLp 𝕜 p :=
  ∑ k ∈ S, a k • lpHaarNormalizedVector 𝕜 p (some ⟨n, k⟩)

theorem operatorReductionRawHaarPacket_ae (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜) :
    operatorReductionRawHaarPacket 𝕜 p n S a =ᵐ[unitIntervalMeasure]
      operatorReductionRawPacketFunction n S a := by
  have hterm (k : Fin (2 ^ n)) : a k • lpHaarDyadic 𝕜 p n k =ᵐ[unitIntervalMeasure]
      fun x => a k * lpHaarFunction 𝕜
        (lpHaarCell (n + 1) (2 * k.val)) (lpHaarCell (n + 1) (2 * k.val + 1)) x := by
    filter_upwards [Lp.coeFn_smul (a k) (lpHaarDyadic 𝕜 p n k),
      lpHaarVector_coe (𝕜 := 𝕜) (p := p.val) (μ := unitIntervalMeasure)
        (lpHaarCell (n + 1) (2 * k.val)) (lpHaarCell (n + 1) (2 * k.val + 1))
        measurableSet_Ioc measurableSet_Ioc] with x hsmul hhaar
    rw [hsmul, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun z => a k * z) hhaar
  filter_upwards [scalarLp_sum_ae (p := p.val) S (fun k => a k • lpHaarDyadic 𝕜 p n k),
    ae_all_iff.mpr hterm] with x hs ht
  exact hs.trans (Finset.sum_congr rfl (fun k _ => ht k))

end SurveyStatements.P5
