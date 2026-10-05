import JLMS.NormalizedBlocks

/-!
# Pointwise asymptotic radii of bounded dual sequences

The radius is the smallest eventual pointwise norm bound on the primal
unit ball. It is zero exactly when the sequence is weak-star null. Ordered
normalized blocking cannot increase the radius. This norm formulation
works over both scalar fields and supports the Hagler–Johnson stabilization.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def DualEventualBound (f : ℕ → (X →L[𝕜] 𝕜)) (r : ℝ) : Prop :=
  ∀ x : X, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, ‖f n x‖ ≤ (r + ε) * ‖x‖

def dualAsymptoticRadius (f : ℕ → (X →L[𝕜] 𝕜)) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ DualEventualBound f r}

theorem dualEventualBound_of_uniform (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ C) : DualEventualBound f C := by
  intro x ε hε
  apply Filter.Eventually.of_forall
  intro n
  exact ((f n).le_opNorm x).trans (mul_le_mul_of_nonneg_right
    ((hf n).trans (by linarith)) (norm_nonneg x))

theorem dualAsymptoticRadius_nonneg (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) : 0 ≤ dualAsymptoticRadius f := by
  change 0 ≤ sInf {r : ℝ | 0 ≤ r ∧ DualEventualBound f r}
  exact le_csInf (s := {r : ℝ | 0 ≤ r ∧ DualEventualBound f r})
    ⟨C, hC, dualEventualBound_of_uniform f hf⟩ (fun r hr => hr.1)

theorem dualAsymptoticRadius_le (f : ℕ → (X →L[𝕜] 𝕜)) {r : ℝ}
    (hr : 0 ≤ r) (hf : DualEventualBound f r) : dualAsymptoticRadius f ≤ r :=
  csInf_le ⟨0, fun s hs => hs.1⟩ ⟨hr, hf⟩

theorem dualAsymptoticRadius_eventualBound (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) : DualEventualBound f (dualAsymptoticRadius f) := by
  intro x ε hε
  have hne : ({r : ℝ | 0 ≤ r ∧ DualEventualBound f r} : Set ℝ).Nonempty :=
    ⟨C, hC, dualEventualBound_of_uniform f hf⟩
  obtain ⟨r, hr, hsmall⟩ := exists_lt_of_csInf_lt hne
    (show dualAsymptoticRadius f < dualAsymptoticRadius f + ε / 2 by linarith)
  filter_upwards [hr.2 x (ε / 2) (half_pos hε)] with n hn
  exact hn.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))

theorem dualEventualBound_blocks (f : ℕ → (X →L[𝕜] 𝕜)) {r : ℝ}
    (hf : DualEventualBound f r) (b : NormalizedBlockSystem 𝕜) :
    DualEventualBound (b.applyDual f) r := by
  intro x ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf x ε hε)
  filter_upwards [eventually_ge_atTop N] with n hn
  calc
    ‖b.applyDual f n x‖ ≤ ∑ k ∈ b.support n, ‖b.coefficient n k‖ * ‖f k x‖ := by
      change ‖dualFiniteBlock f (b.support n) (b.coefficient n) x‖ ≤ _
      simp only [dualFiniteBlock, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ ∑ k ∈ b.support n, ‖b.coefficient n k‖ * ((r + ε) * ‖x‖) :=
      Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
        (hN k (hn.trans (b.index_le_support n k hk))) (norm_nonneg _))
    _ = (r + ε) * ‖x‖ := by rw [← Finset.sum_mul, b.mass_one, one_mul]

theorem dualAsymptoticRadius_blocks_le (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (b : NormalizedBlockSystem 𝕜) :
    dualAsymptoticRadius (b.applyDual f) ≤ dualAsymptoticRadius f :=
  dualAsymptoticRadius_le _ (dualAsymptoticRadius_nonneg f hC hf)
    (dualEventualBound_blocks f (dualAsymptoticRadius_eventualBound f hC hf) b)

theorem dualEventualBound_zero_of_null (f : ℕ → (X →L[𝕜] 𝕜))
    (hf : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0)) : DualEventualBound f 0 := by
  intro x ε hε
  by_cases hx : x = 0
  · subst x; simp
  · have hεx : 0 < ε * ‖x‖ := mul_pos hε (norm_pos_iff.mpr hx)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hf x) (ε * ‖x‖) hεx
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [zero_add, dist_zero_right] using (hN n hn).le

theorem dualAsymptoticRadius_eq_zero_iff (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) :
    dualAsymptoticRadius f = 0 ↔ ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0) := by
  constructor
  · intro hr x
    have hb := dualAsymptoticRadius_eventualBound f hC hf
    rw [hr] at hb
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let η := (ε / 2) / (‖x‖ + 1)
    have hη : 0 < η := div_pos (half_pos hε) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hb x η hη)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_zero_right]
    calc
      _ ≤ η * ‖x‖ := by simpa only [zero_add] using hN n hn
      _ ≤ η * (‖x‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
      _ = ε / 2 := div_mul_cancel₀ _ (by positivity)
      _ < ε := half_lt_self hε
  · intro h
    exact le_antisymm (dualAsymptoticRadius_le f (by norm_num)
      (dualEventualBound_zero_of_null f h)) (dualAsymptoticRadius_nonneg f hC hf)

end JLMS
