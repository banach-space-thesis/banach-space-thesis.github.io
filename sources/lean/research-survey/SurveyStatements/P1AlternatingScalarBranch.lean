import SurveyStatements.P1ScalarClusterPairs

/-! Two actual scalar cluster values yield an increasing branch alternating
between their prescribed neighbourhoods. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

theorem scalar_cluster_exists_far_close (u : ℕ → ℂ) {z : ℂ} {p : ℕ → ℕ}
    (hp : Tendsto p atTop atTop) (hz : Tendsto (u ∘ p) atTop (𝓝 z))
    {τ : ℝ} (hτ : 0 < τ) (B : ℕ) :
    ∃ i : ℕ, B < i ∧ ‖u i - z‖ < τ := by
  have hfar := hp.eventually (eventually_gt_atTop B)
  have hclose := (Metric.tendsto_nhds.mp hz) τ hτ
  obtain ⟨k, hk⟩ := (hfar.and hclose).exists
  exact ⟨p k, hk.1, by simpa only [Function.comp_apply, dist_eq_norm] using hk.2⟩

theorem scalar_clusters_exists_alternating_branch (u : ℕ → ℂ) (z w : ℂ)
    (p q : ℕ → ℕ) (hp : Tendsto p atTop atTop) (hq : Tendsto q atTop atTop)
    (hz : Tendsto (u ∘ p) atTop (𝓝 z)) (hw : Tendsto (u ∘ q) atTop (𝓝 w))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ n, ‖u (ν n) - (if n % 2 = 0 then z else w)‖ < τ := by
  classical
  have hex (n B : ℕ) : ∃ i : ℕ, B < i ∧
      ‖u i - (if n % 2 = 0 then z else w)‖ < τ := by
    split_ifs
    · exact scalar_cluster_exists_far_close u hp hz hτ B
    · exact scalar_cluster_exists_far_close u hq hw hτ B
  choose next hfar hclose using hex
  let ν : ℕ → ℕ := Nat.rec (next 0 0) (fun n i => next (n + 1) i)
  have hrec (n : ℕ) : ν (n + 1) = next (n + 1) (ν n) := rfl
  refine ⟨ν, strictMono_nat_of_lt_succ (fun n => ?_), ?_⟩
  · rw [hrec]
    exact hfar (n + 1) (ν n)
  · intro n
    cases n with
    | zero => exact hclose 0 0
    | succ n => exact hclose (n + 1) (ν n)

theorem bounded_complex_not_cauchy_exists_alternating_branch (u : ℕ → ℂ) {M : ℝ}
    (hM : ∀ n, ‖u n‖ ≤ M) (hnot : ¬ CauchySeq u) {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ z w : ℂ, ‖z‖ ≤ M ∧ δ ≤ ‖w‖ ∧
      ∃ ν : ℕ → ℕ, StrictMono ν ∧
        ∀ n, ‖u (ν n) - (z + if n % 2 = 0 then 0 else w)‖ < τ := by
  obtain ⟨δ, hδ, z, w, hzM, hwM, hzw, p, q, hp, hq, hz, hw⟩ :=
    bounded_complex_not_cauchy_cluster_pair u hM hnot
  obtain ⟨ν, hν, hclose⟩ := scalar_clusters_exists_alternating_branch u z w p q hp hq hz hw hτ
  refine ⟨δ, hδ, z, w - z, hzM, ?_, ν, hν, ?_⟩
  · simpa only [norm_sub_rev] using hzw
  · intro n
    convert hclose n using 1
    split_ifs <;> simp

end SurveyStatements.P1
