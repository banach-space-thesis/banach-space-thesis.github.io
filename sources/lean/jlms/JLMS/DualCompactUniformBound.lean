import JLMS.DualAsymptoticRadius
import JLMS.FiniteRank

/-!
# Compact-set uniformization of eventual dual bounds

The functionals share a Lipschitz bound. A finite compact ball cover turns
pointwise eventual estimates into an eventual estimate uniform on the set.
This is the quantifier-permutation step in the Hagler–Johnson construction.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem dualEventualBound_uniform_compact (f : ℕ → (X →L[𝕜] 𝕜)) {C r ε : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (hr : 0 ≤ r)
    (hb : DualEventualBound f r) (hε : 0 < ε)
    (S : Set X) (hS : IsCompact S) (hunit : ∀ x ∈ S, ‖x‖ ≤ 1) :
    ∀ᶠ n in atTop, ∀ x ∈ S, ‖f n x‖ ≤ r + ε := by
  let ρ := (ε / 2) / (C + 1)
  have hρ : 0 < ρ := div_pos (half_pos hε) (by linarith)
  obtain ⟨t, htS, htf, hcover⟩ := hS.finite_cover_balls hρ
  have hev : ∀ᶠ n in atTop, ∀ y ∈ t, ‖f n y‖ ≤ (r + ε / 2) * ‖y‖ :=
    htf.eventually_all.mpr (fun y hy => hb y (ε / 2) (half_pos hε))
  filter_upwards [hev] with n hn
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hdist : ‖x - y‖ < ρ := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  have hyunit := hunit y (htS hy)
  have hsmall : C * ‖x - y‖ ≤ ε / 2 := by
    calc
      _ ≤ C * ρ := mul_le_mul_of_nonneg_left hdist.le hC
      _ ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ.le
      _ = ε / 2 := by dsimp [ρ]; field_simp
  have hyb : ‖f n y‖ ≤ r + ε / 2 := (hn y hy).trans (by
    simpa using mul_le_mul_of_nonneg_left hyunit (by positivity : 0 ≤ r + ε / 2))
  calc
    ‖f n x‖ ≤ ‖f n (x - y)‖ + ‖f n y‖ := by
      have heq : f n x = f n (x - y) + f n y := by simp
      rw [heq]
      exact norm_add_le _ _
    _ ≤ C * ‖x - y‖ + (r + ε / 2) := add_le_add
      (((f n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _))) hyb
    _ ≤ r + ε := by linarith

theorem dualEventualBound_finiteDimensional_restriction
    (f : ℕ → (X →L[𝕜] 𝕜)) {C r ε : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) (hr : 0 ≤ r) (hb : DualEventualBound f r)
    (hε : 0 < ε) (D : Submodule 𝕜 X) [FiniteDimensional 𝕜 D] :
    ∀ᶠ n in atTop, ‖(f n).comp D.subtypeL‖ ≤ r + ε := by
  let g (n : ℕ) := (f n).comp D.subtypeL
  have hg (n : ℕ) : ‖g n‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro x
    exact ((f n).le_opNorm x.val).trans
      (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg x.val))
  have hgb : DualEventualBound g r := fun x η hη => hb x.val η hη
  have he := dualEventualBound_uniform_compact g hC hg hr hgb hε
    (Metric.closedBall (0 : D) 1) (isCompact_closedBall _ _) (fun x hx => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  filter_upwards [he] with n hn
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity : 0 ≤ r + ε)
  intro x hx
  exact hn x (by simpa only [Metric.mem_closedBall, dist_zero_right, hx] using (le_refl (1 : ℝ)))

end JLMS
