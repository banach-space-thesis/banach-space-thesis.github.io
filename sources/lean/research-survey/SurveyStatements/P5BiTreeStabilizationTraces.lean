import SurveyStatements.P5BiTreeStabilizationBalance
import SurveyStatements.P5Support.LpHaarNormalizedTraces

/-! Bounded finitely additive traces on the dyadic algebra, simultaneous
countable extraction, and normalized finite-family signed split selection. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

structure DyadicTrace (𝕜 : Type*) [RCLike 𝕜] (M : ℝ) where
  value : LpHaarDyadicSetIndex → 𝕜
  norm_le : ∀ i, ‖value i‖ ≤
    M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i)
  congr : ∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → value i = value j
  additive : ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
    lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j →
      value k = value i + value j

theorem countable_trace_cluster {A : Type*} [Countable A]
    (d : A → (n : ℕ) → Fin (2 ^ n) → 𝕜)
    {M : ℝ} (hM : 0 ≤ M) (hd : ∀ α n k, ‖d α n k‖ ≤ M)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels) :
    ∃ a : A → DyadicTrace 𝕜 M, ∃ r : ℕ → ℕ, StrictMono r ∧
      ∀ α i, Tendsto (fun n =>
        lpHaarLevelTrace (d α) (levels (r n)) (lpHaarDyadicSet i))
          atTop (𝓝 ((a α).value i)) := by
  have hv (n : ℕ) (x : A × LpHaarDyadicSetIndex) :
      ‖lpHaarLevelTrace (d x.1) (levels n) (lpHaarDyadicSet x.2)‖ ≤ M := by
    have h := lpHaarLevelTrace_norm_le (d x.1) hM (hd x.1)
      (levels n) _ (lpHaarDyadicSet_measurable x.2)
    have hmeasure :
        (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet x.2) ≤ 1 := by
      simpa using (measureReal_mono
        (μ := volume.restrict (Icc (0 : ℝ) 1)) (subset_univ (lpHaarDyadicSet x.2)))
    exact h.trans (by nlinarith)
  obtain ⟨a, r, hr, _, ha⟩ := haar_countable_trace_cluster
    (fun n (x : A × LpHaarDyadicSetIndex) =>
      lpHaarLevelTrace (d x.1) (levels n) (lpHaarDyadicSet x.2)) hv
  have hbound (α : A) (i : LpHaarDyadicSetIndex) :
      ‖a (α, i)‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i) :=
    le_of_tendsto (ha (α, i)).norm (Eventually.of_forall (fun n =>
      lpHaarLevelTrace_norm_le (d α) hM (hd α) (levels (r n)) _
        (lpHaarDyadicSet_measurable i)))
  have heq (α : A) (i j : LpHaarDyadicSetIndex)
      (hij : lpHaarDyadicSet i = lpHaarDyadicSet j) : a (α, i) = a (α, j) := by
    apply tendsto_nhds_unique (ha (α, i))
    simpa only [hij] using ha (α, j)
  have hadd (α : A) (i j k : LpHaarDyadicSetIndex)
      (hdis : Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j))
      (hunion : lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j) :
      a (α, k) = a (α, i) + a (α, j) := by
    apply tendsto_nhds_unique (ha (α, k))
    convert (ha (α, i)).add (ha (α, j)) using 1
    funext n
    rw [hunion, lpHaarLevelTrace_union (d α) (levels (r n)) _ _
      (lpHaarDyadicSet_measurable i) (lpHaarDyadicSet_measurable j) hdis]
  exact ⟨fun α => ⟨fun i => a (α, i), hbound α, heq α, hadd α⟩,
    r, hr, fun α i => ha (α, i)⟩

theorem simultaneous_trace_parent_select {m : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (a : Fin m → DyadicTrace 𝕜 M)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (Good : ℕ → Prop) (hgood : ∀ᶠ n in atTop, Good (levels n))
    (P : LpHaarFiniteParent) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧ Good S.level ∧
      ∀ r b, ‖lpHaarParentTrace (a r).value (S.child b) -
        lpHaarParentTrace (a r).value P‖ < ε := by
  let mass := (volume.restrict (Icc (0 : ℝ) 1)).real P.set
  have hmass : 0 < mass := P.mass_pos
  have hδ : 0 < ε * mass / 2 := by positivity
  have hmesh : Tendsto (fun t => (m : ℝ) *
      (M ^ 2 * intervalLpDyadicRadius (levels t))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((lpHaarDyadicRadius_tendsto.comp hlevels.tendsto_atTop).const_mul
        (M ^ 2)).const_mul (m : ℝ)
  have hn : ∀ᶠ t in atTop, max N P.level ≤ levels t :=
    hlevels.tendsto_atTop.eventually (eventually_ge_atTop _)
  have hs : ∀ᶠ t in atTop, (m : ℝ) *
      (M ^ 2 * intervalLpDyadicRadius (levels t)) < (2 * (ε * mass / 2)) ^ 2 :=
    (tendsto_order.mp hmesh).2 _ (sq_pos_of_pos (mul_pos (by norm_num) hδ))
  obtain ⟨t, hgood, hn, hs⟩ := (hgood.and (hn.and hs)).exists
  let A := lpHaarRefineAt P.level P.atoms (levels t)
  have hparent : lpHaarBlockParent (levels t) A = P.set :=
    lpHaarRefineAt_parent P.level P.atoms (levels t) ((le_max_right _ _).trans hn)
  have hA : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : mass = 0 := by
      dsimp only [mass]
      rw [← hparent, he]
      simp [lpHaarBlockParent]
    exact hmass.ne' hz
  obtain ⟨θ, hθ⟩ := simultaneous_trace_balanced_split
    (fun r => (a r).value) (fun r => (a r).additive) hM
    (fun r => (a r).norm_le) (levels t) A hδ hs
  let S : LpHaarFiniteSplit := ⟨levels t, A, θ, hA⟩
  have hP : S.parent.set = P.set := hparent
  refine ⟨S, (le_max_left _ _).trans hn, hP, hgood, ?_⟩
  intro r b
  have hval : (a r).value ⟨levels t, A⟩ = (a r).value P.index :=
    (a r).congr _ _ hparent
  have hc : ‖(a r).value (S.child b).index -
      (2 : 𝕜)⁻¹ * (a r).value P.index‖ < ε * mass / 2 := by
    cases b
    · simpa only [S, LpHaarFiniteSplit.child, Bool.false_eq_true, if_false,
        LpHaarFiniteParent.index, hval] using (hθ r).2
    · simpa only [S, LpHaarFiniteSplit.child, if_true,
        LpHaarFiniteParent.index, hval] using (hθ r).1
  have hchild : ((volume.restrict (Icc (0 : ℝ) 1)).real (S.child b).set : 𝕜) =
      (mass : 𝕜) / 2 := by
    rw [S.child_mass, hP]
    push_cast
    rfl
  have hid : lpHaarParentTrace (a r).value (S.child b) -
      lpHaarParentTrace (a r).value P =
      ((a r).value (S.child b).index - (2 : 𝕜)⁻¹ * (a r).value P.index) /
        ((mass : 𝕜) / 2) := by
    unfold lpHaarParentTrace
    rw [hchild]
    change _ / ((mass : 𝕜) / 2) - _ / (mass : 𝕜) = _
    have hmc : (mass : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hmass.ne'
    field_simp
  rw [hid, norm_div, norm_div, RCLike.norm_ofReal, abs_of_pos hmass]
  have htwo : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  apply (div_lt_iff₀ (div_pos hmass (by norm_num))).mpr
  simpa only [mul_div_assoc] using hc

end SurveyStatements.P5.BiTree
