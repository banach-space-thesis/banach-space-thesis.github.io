import ThesisCommon.Analysis.JamesFarPathVariation
import ThesisCommon.Analysis.JamesTailPathEstimate

/-! The ordered coordinate truncations converge in the actual James norm.
The proof first bounds the tail by its far-path variation, including the
boundary term of a path crossing the truncation point. -/
noncomputable section
open Filter Topology
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}

theorem james_far_coordinate_le (x : JamesSequenceSpace 𝕜 p) (N : ℕ) {C : ℝ}
    (hfar : ∀ s : JamesPath, N < s.index 0 → ‖jamesPathMap 𝕜 p s x.val‖ ≤ C)
    {n : ℕ} (hn : N < n) : ‖x n‖ ≤ C := by
  have ht : Tendsto (fun m => ‖x n - x m‖) atTop (𝓝 ‖x n‖) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub x.tendsto_zero).norm
  apply le_of_tendsto ht
  filter_upwards [eventually_gt_atTop n] with m hm
  exact (jamesPath_two_difference_le 𝕜 p x.val n m hm).trans
    (hfar (JamesPath.two n m hm) (by simpa [JamesPath.two] using hn))

theorem james_tail_norm_le_far (x : JamesSequenceSpace 𝕜 p) (N : ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (hfar : ∀ s : JamesPath, N < s.index 0 → ‖jamesPathMap 𝕜 p s x.val‖ ≤ C) :
    ‖JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) N x‖ ≤ 2 * C := by
  classical
  apply JamesSequenceSpace.norm_le
  intro s
  by_cases hzero : N < s.index 0
  · have heq : jamesPathMap 𝕜 p s (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) N x).val =
        jamesPathMap 𝕜 p s x.val := by
      ext r
      have hl : N < s.index r.castSucc :=
        hzero.trans_le (s.strictMono.monotone (Fin.zero_le _))
      have hr : N < s.index r.succ :=
        hzero.trans_le (s.strictMono.monotone (Fin.zero_le _))
      simp only [jamesPathMap_apply, JamesSequenceSpace.tail_apply, if_neg hl.not_ge,
        if_neg hr.not_ge]
    rw [heq]
    exact (hfar s hzero).trans (by linarith)
  · by_cases hex : ∃ j : ℕ, ∃ hj : j < s.length + 1, N < s.index ⟨j, hj⟩
    · let j : Fin (s.length + 1) := ⟨Nat.find hex, (Nat.find_spec hex).choose⟩
      have hafter : N < s.index j := (Nat.find_spec hex).choose_spec
      have hj : 0 < j.val := by
        by_contra hn
        have hj0 : j = 0 := Fin.ext (by dsimp [j] at *; omega)
        exact hzero (hj0 ▸ hafter)
      have hbefore (i : Fin (s.length + 1)) (hi : i.val < j.val) : s.index i ≤ N := by
        by_contra hn
        have hh : ∃ hi' : i.val < s.length + 1, N < s.index ⟨i.val, hi'⟩ :=
          ⟨i.isLt, Nat.lt_of_not_ge hn⟩
        have hmin := Nat.find_min' hex hh
        change Nat.find hex ≤ i.val at hmin
        dsimp [j] at hi
        omega
      apply (james_tail_path_norm_le_suffix x N s j hj hbefore hafter).trans
      have hs : ‖jamesPathMap 𝕜 p (s.suffix j) x.val‖ ≤ C :=
        hfar (s.suffix j) (by simpa [JamesPath.suffix] using hafter)
      have hc := james_far_coordinate_le x N hfar hafter
      linarith
    · have heq : jamesPathMap 𝕜 p s
          (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) N x).val = 0 := by
        ext r
        have hall (i : Fin (s.length + 1)) : s.index i ≤ N := by
          by_contra hn
          exact hex ⟨i.val, i.isLt, Nat.lt_of_not_ge hn⟩
        simp [jamesPathMap_apply, JamesSequenceSpace.tail_apply, hall]
      rw [heq, norm_zero]
      positivity

namespace JamesSequenceSpace

/-- Norm convergence of the actual initial projections, for every finite p ≥ 1. -/
theorem initial_tendsto (hp : p.val ≠ ∞) (x : JamesSequenceSpace 𝕜 p) :
    Tendsto (fun N => initial (𝕜 := 𝕜) (p := p) N x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := james_far_path_small hp x (show 0 < ε / 4 by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound : ‖tail (𝕜 := 𝕜) (p := p) n x‖ ≤ 2 * (ε / 4) :=
    james_tail_norm_le_far x n (by positivity)
      (fun s hs => (hN s (hn.trans_lt hs)).le)
  have heq : dist (initial (𝕜 := 𝕜) (p := p) n x) x = ‖tail (𝕜 := 𝕜) (p := p) n x‖ := by
    rw [dist_eq_norm, norm_sub_rev]
    rfl
  rw [heq]
  linarith

end JamesSequenceSpace
end ThesisCommon
