import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stability prerequisites for ℓ₁ sums

Direct norm-limit formulas for the concrete ℓ₁ sum of finite-dimensional
spaces. These formulas avoid constructing the Johnson–Zippin space.
-/

noncomputable section

open Filter Topology
open scoped NNReal ENNReal

namespace LindenstraussRetraction

universe u v w

variable {I : Type u} {B : I → Type v} [∀ i, NormedAddCommGroup (B i)]

/-- The norm on a dependent ℓ₁ sum is the sum of the coordinate norms. -/
theorem l1_hasSum_norm (x : lp B 1) : HasSum (fun i => ‖x i‖) ‖x‖ := by
  simpa using lp.hasSum_norm (E := B) (p := (1 : ℝ≥0∞)) (by norm_num) x

/-- Under coordinatewise convergence, the difference of two ℓ₁ norms has a
limit even when the vectors need not converge in the ℓ₁ norm. -/
theorem l1_tendsto_norm_add_sub_norm
    {A : Type w} {l : Filter A} {F : A → lp B 1} {x : lp B 1}
    (hF : ∀ i, Tendsto (fun a => F a i) l (𝓝 (x i))) (y : lp B 1) :
    Tendsto (fun a => ‖F a + y‖ - ‖F a‖) l (𝓝 (‖x + y‖ - ‖x‖)) := by
  have hsum (z : lp B 1) :
      (∑' i, (‖z i + y i‖ - ‖z i‖)) = ‖z + y‖ - ‖z‖ := by
    simpa only [lp.coeFn_add, Pi.add_apply] using
      ((l1_hasSum_norm (z + y)).sub (l1_hasSum_norm z)).tsum_eq
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun a i => ‖F a i + y i‖ - ‖F a i‖)
    (g := fun i => ‖x i + y i‖ - ‖x i‖)
    (bound := fun i => ‖y i‖) (l1_hasSum_norm y).summable
    (fun i => ((hF i).add_const (y i)).norm.sub (hF i).norm)
    (Eventually.of_forall (fun a i => by
      rw [Real.norm_eq_abs]
      have h := abs_norm_sub_norm_le (F a i + y i) (F a i)
      simpa only [add_sub_cancel_left] using h))
  simpa only [hsum] using h

/-- A bounded family in an ℓ₁ sum of proper spaces has a coordinatewise
ultrafilter limit which still belongs to the ℓ₁ sum. -/
theorem l1_exists_ultrafilter_coordinate_limit
    [∀ i, ProperSpace (B i)] {A : Type w} (U : Ultrafilter A)
    (F : A → lp B 1) {C : ℝ} (hC : ∀ a, ‖F a‖ ≤ C) :
    ∃ x : lp B 1, ‖x‖ ≤ C ∧ ∀ i, Tendsto (fun a => F a i) U (𝓝 (x i)) := by
  classical
  have hcoord (i : I) : ∃ x : B i, ‖x‖ ≤ C ∧ Tendsto (fun a => F a i) U (𝓝 x) := by
    obtain ⟨x, hx, hlim⟩ := (isCompact_closedBall (0 : B i) C).ultrafilter_le_nhds
      (U.map (fun a => F a i)) (by
        rw [le_principal_iff]
        change ∀ᶠ a in (U : Filter A), F a i ∈ Metric.closedBall 0 C
        exact Eventually.of_forall (fun a => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (lp.norm_apply_le_norm (by norm_num) (F a) i).trans (hC a)))
    exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, hlim⟩
  choose x hx hlim using hcoord
  have hpointwise : Tendsto (fun a => (F a : ∀ i, B i)) U (𝓝 x) :=
    tendsto_pi_nhds.2 hlim
  have hbounded : Bornology.IsBounded (Set.range F) :=
    isBounded_iff_forall_norm_le.2 ⟨C, fun z hz => by obtain ⟨a, rfl⟩ := hz; exact hC a⟩
  let z : lp B 1 := ⟨x, lp.memℓp_of_tendsto hbounded hpointwise⟩
  exact ⟨z, lp.norm_le_of_tendsto (Eventually.of_forall hC) hpointwise, hlim⟩

/-- Each bounded ultrafilter family in an ℓ₁ sum of proper spaces has a
distance-limit type of the form `y ↦ ‖x - y‖ + r`, with `r ≥ 0`. -/
theorem l1_exists_ultrafilter_distance_type
    [∀ i, ProperSpace (B i)] {A : Type w} (U : Ultrafilter A)
    (F : A → lp B 1) {C : ℝ} (hC : ∀ a, ‖F a‖ ≤ C) :
    ∃ (x : lp B 1) (r : ℝ), 0 ≤ r ∧ ‖x‖ + r ≤ C ∧
      ∀ y : lp B 1, Tendsto (fun a => ‖F a - y‖) U (𝓝 (‖x - y‖ + r)) := by
  obtain ⟨x, _, hx⟩ := l1_exists_ultrafilter_coordinate_limit U F hC
  obtain ⟨b, hb, hb_lim⟩ := isCompact_Icc.ultrafilter_le_nhds
    (U.map (fun a => ‖F a‖)) (by
      rw [le_principal_iff]
      change ∀ᶠ a in (U : Filter A), ‖F a‖ ∈ Set.Icc 0 C
      exact Eventually.of_forall (fun a => ⟨norm_nonneg _, hC a⟩))
  have htype (y : lp B 1) :
      Tendsto (fun a => ‖F a - y‖) U (𝓝 (‖x - y‖ + (b - ‖x‖))) := by
    have h := (l1_tendsto_norm_add_sub_norm hx (-y)).add hb_lim
    convert h using 1
    · ext a
      simp only [← sub_eq_add_neg, sub_add_cancel]
    · congr 1
      rw [← sub_eq_add_neg]
      ring
  have hr : 0 ≤ b - ‖x‖ := by
    have h := ge_of_tendsto (htype x) (Eventually.of_forall (fun a => norm_nonneg (F a - x)))
    simpa only [sub_self, norm_zero, zero_add] using h
  exact ⟨x, b - ‖x‖, hr, by linarith [hb.2], htype⟩

/-- Bounded distance arrays in ℓ₁ sums of proper spaces have equal iterated
ultrafilter limits. This supplies the stable-norm ingredient directly. -/
theorem l1_ultrafilter_double_limit_eq
    [∀ i, ProperSpace (B i)] {A : Type w} {D : Type*}
    (U : Ultrafilter A) (V : Ultrafilter D)
    (F : A → lp B 1) (G : D → lp B 1)
    {C₁ C₂ : ℝ} (hF : ∀ a, ‖F a‖ ≤ C₁) (hG : ∀ b, ‖G b‖ ≤ C₂)
    {p : A → ℝ} {q : D → ℝ} {a b : ℝ}
    (hp : ∀ i, Tendsto (fun j => ‖F i - G j‖) V (𝓝 (p i)))
    (hq : ∀ j, Tendsto (fun i => ‖F i - G j‖) U (𝓝 (q j)))
    (ha : Tendsto p U (𝓝 a)) (hb : Tendsto q V (𝓝 b)) : a = b := by
  obtain ⟨x, r, _, _, hx⟩ := l1_exists_ultrafilter_distance_type U F hF
  obtain ⟨y, s, _, _, hy⟩ := l1_exists_ultrafilter_distance_type V G hG
  have hp_eq (i : A) : p i = ‖F i - y‖ + s :=
    tendsto_nhds_unique (hp i) (by simpa only [norm_sub_rev] using hy (F i))
  have hq_eq (j : D) : q j = ‖x - G j‖ + r :=
    tendsto_nhds_unique (hq j) (hx (G j))
  have hp_fun : p = fun i => ‖F i - y‖ + s := funext hp_eq
  have hq_fun : q = fun j => ‖x - G j‖ + r := funext hq_eq
  have ha' : a = ‖x - y‖ + r + s :=
    tendsto_nhds_unique ha (by rw [hp_fun]; exact (hx y).add_const s)
  have hb' : b = ‖x - y‖ + s + r :=
    tendsto_nhds_unique hb (by rw [hq_fun]; simpa only [norm_sub_rev] using (hy x).add_const r)
  rw [ha', hb']
  ring

/-- The sequential double-limit identity for bounded sequences, the usual
stable-norm condition needed for the summation space. -/
theorem l1_bounded_sequences_double_limit_eq
    [∀ i, ProperSpace (B i)] (F G : ℕ → lp B 1)
    {C₁ C₂ : ℝ} (hF : ∀ n, ‖F n‖ ≤ C₁) (hG : ∀ n, ‖G n‖ ≤ C₂)
    {p q : ℕ → ℝ} {a b : ℝ}
    (hp : ∀ i, Tendsto (fun j => ‖F i - G j‖) atTop (𝓝 (p i)))
    (hq : ∀ j, Tendsto (fun i => ‖F i - G j‖) atTop (𝓝 (q j)))
    (ha : Tendsto p atTop (𝓝 a)) (hb : Tendsto q atTop (𝓝 b)) : a = b := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  exact l1_ultrafilter_double_limit_eq U U F G hF hG
    (fun i => (hp i).mono_left hU) (fun j => (hq j).mono_left hU)
    (ha.mono_left hU) (hb.mono_left hU)

end LindenstraussRetraction
