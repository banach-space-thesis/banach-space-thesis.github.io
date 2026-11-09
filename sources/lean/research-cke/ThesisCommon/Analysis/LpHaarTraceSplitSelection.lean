import ThesisCommon.Analysis.LpHaarTraceBalancing
import ThesisCommon.Analysis.LpHaarTraceLimit
import ThesisCommon.Analysis.LpHaarFiniteSplits
import ThesisCommon.Analysis.LpHaarContinuousApproximation

/-! Trace-balanced genuine signed splits of any prescribed dyadic parent.
The common trace subsequence also controls the diagonal average of the
selected block. All choices are made from the parent and a lower level bound. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def LpHaarFiniteParent.index (P : LpHaarFiniteParent) : LpHaarDyadicSetIndex :=
  ⟨P.level, P.atoms⟩

theorem lpHaarLevelTrace_parent (d : ∀ n, Fin (2 ^ n) → 𝕜)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    lpHaarLevelTrace d n (lpHaarBlockParent n S) =
      (intervalLpDyadicRadius n : 𝕜) * ∑ k ∈ S, d n k := by
  have hinter (k : Fin (2 ^ n)) : lpHaarBlockParent n S ∩ lpHaarCell n k =
      if k ∈ S then lpHaarCell n k else ∅ := by
    by_cases hk : k ∈ S
    · rw [if_pos hk]
      apply inter_eq_right.mpr
      intro x hx
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, hx⟩⟩
    · rw [if_neg hk]
      apply Set.disjoint_iff_inter_eq_empty.mp
      apply Set.disjoint_left.mpr
      intro x hx hy
      change x ∈ ⋃ j ∈ S, lpHaarCell n j at hx
      obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hj, hx⟩ := mem_iUnion.mp hx
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      exact Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel n
        (fun h => hjk (Fin.ext h))) hx hy
  unfold lpHaarLevelTrace
  have hterm (k : Fin (2 ^ n)) :
      ((volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S ∩ lpHaarCell n k) : 𝕜) * d n k =
        if k ∈ S then (intervalLpDyadicRadius n : 𝕜) * d n k else 0 := by
    rw [hinter]
    by_cases hk : k ∈ S
    · rw [if_pos hk, if_pos hk]
      congr 2
      rw [measureReal_def, lpHaarCell_measure n k k.isLt,
        ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]
    · simp [hk]
  simp_rw [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem lpHaar_trace_parent_select
    (d : ∀ n, Fin (2 ^ n) → 𝕜) (a : LpHaarDyadicSetIndex → 𝕜)
    (r : ℕ → ℕ) (hr : StrictMono r) {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, ‖a i‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i))
    (hlim : ∀ i, Tendsto (fun t => lpHaarLevelTrace d (r t) (lpHaarDyadicSet i)) atTop (𝓝 (a i)))
    (heq : ∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → a i = a j)
    (hadd : ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
      lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j → a k = a i + a j)
    (P : LpHaarFiniteParent) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
      ‖lpHaarLevelTrace d S.level S.parent.set - a P.index‖ <
        ε * (volume.restrict (Icc (0 : ℝ) 1)).real P.set ∧
      ∀ b : Bool, ‖a (S.child b).index - (2 : 𝕜)⁻¹ * a P.index‖ <
        ε * (volume.restrict (Icc (0 : ℝ) 1)).real P.set / 2 := by
  let m := (volume.restrict (Icc (0 : ℝ) 1)).real P.set
  have hm : 0 < m := P.mass_pos
  have hδ : 0 < ε * m / 2 := by positivity
  have htrace : Tendsto (fun t => ‖lpHaarLevelTrace d (r t) P.set - a P.index‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((hlim P.index).sub (tendsto_const_nhds (x := a P.index))).norm
  have hmesh : Tendsto (fun t => M ^ 2 * intervalLpDyadicRadius (r t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (lpHaarDyadicRadius_tendsto.comp hr.tendsto_atTop).const_mul (M ^ 2)
  have ht : ∀ᶠ t in atTop, ‖lpHaarLevelTrace d (r t) P.set - a P.index‖ < ε * m :=
    (tendsto_order.mp htrace).2 _ (mul_pos hε hm)
  have hn : ∀ᶠ t in atTop, max N P.level ≤ r t :=
    hr.tendsto_atTop.eventually (eventually_ge_atTop _)
  have hs : ∀ᶠ t in atTop, M ^ 2 * intervalLpDyadicRadius (r t) < (2 * (ε * m / 2)) ^ 2 :=
    (tendsto_order.mp hmesh).2 _ (sq_pos_of_pos (mul_pos (by norm_num) hδ))
  obtain ⟨t, htrace, hn, hs⟩ := (ht.and (hn.and hs)).exists
  let A := lpHaarRefineAt P.level P.atoms (r t)
  have hparent : lpHaarBlockParent (r t) A = P.set :=
    lpHaarRefineAt_parent P.level P.atoms (r t) ((le_max_right _ _).trans hn)
  have hA : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : m = 0 := by
      dsimp only [m]
      rw [← hparent, he]
      simp [lpHaarBlockParent]
    exact hm.ne' hz
  obtain ⟨θ, hl, hr⟩ := lpHaarTrace_balanced_split a hadd hM ha (r t) A hδ hs
  have hval : a ⟨r t, A⟩ = a P.index := heq _ _ hparent
  refine ⟨⟨r t, A, θ, hA⟩, (le_max_left _ _).trans hn, hparent, ?_, ?_⟩
  · change ‖lpHaarLevelTrace d (r t) (lpHaarBlockParent (r t) A) - a P.index‖ < ε * m
    rw [hparent]
    exact htrace
  · intro b
    cases b
    · simpa only [LpHaarFiniteSplit.child, Bool.false_eq_true, if_false,
        LpHaarFiniteParent.index, hval] using hr
    · simpa only [LpHaarFiniteSplit.child, if_true, LpHaarFiniteParent.index, hval] using hl

end ThesisCommon
