import PL1.DunfordPettis
import PL1.LpInclusions

/-!
# Compact restriction and uniform approximation

This isolates the elementary compactness part of the L1 Dunford–Pettis
criterion. The uniform approximation hypothesis is explicit; in the concrete
application it is supplied by uniform integrability of weakly convergent L1
sequences.
-/

noncomputable section
open Filter
open scoped Topology

namespace PL1

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

def HasUniformBoundedApproximations (V : G →L[𝕜] E) (x : ℕ → E) : Prop :=
  ∀ ε > 0, ∃ M : ℝ, ∀ n, ∃ y : G, ‖y‖ ≤ M ∧ ‖x n - V y‖ < ε

theorem totallyBounded_image_of_uniform_approximation
    (T : E →L[𝕜] F) (V : G →L[𝕜] E)
    (hTV : IsCompactOperator (T.comp V)) (x : ℕ → E)
    (hx : HasUniformBoundedApproximations V x) :
    TotallyBounded (Set.range (fun n => T (x n))) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have hδ : 0 < ε / (2 * (‖T‖ + 1)) := by positivity
  obtain ⟨M, hM⟩ := hx _ hδ
  obtain ⟨K, hK, hTK⟩ := hTV.image_subset_compact_of_bounded
    (Metric.isBounded_closedBall (x := (0 : G)) (r := M))
  obtain ⟨D, hD, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (ε / 2) (half_pos hε)
  refine ⟨D, hD, ?_⟩
  rintro z ⟨n, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hM n
  have hyK : T (V y) ∈ K := hTK ⟨y, by simpa only [Metric.mem_closedBall,
    dist_zero_right] using hy, rfl⟩
  obtain ⟨w, hwD, hwy⟩ := Set.mem_iUnion₂.mp (hcover hyK)
  apply Set.mem_iUnion₂.mpr
  refine ⟨w, hwD, ?_⟩
  have hsmall : dist (T (x n)) (T (V y)) < ε / 2 := by
    rw [dist_eq_norm, ← map_sub]
    have hd := (lt_div_iff₀ (show 0 < 2 * (‖T‖ + 1) by positivity)).mp hxy
    have hb := T.le_opNorm (x n - V y)
    nlinarith [norm_nonneg (x n - V y)]
  exact (dist_triangle (T (x n)) (T (V y)) w).trans_lt
    (by have := Metric.mem_ball.mp hwy; linarith)

/-- A compact restriction sends uniformly approximable weak sequences to norm
convergent sequences, by relative compactness and uniqueness of weak limits. -/
theorem weaklyConverges_image_of_compact_restriction [CompleteSpace F]
    (T : E →L[𝕜] F) (V : G →L[𝕜] E)
    (hTV : IsCompactOperator (T.comp V)) {x : ℕ → E} {a : E}
    (hx : WeaklyConverges 𝕜 E x a) (happrox : HasUniformBoundedApproximations V x) :
    Tendsto (fun n => T (x n)) atTop (𝓝 (T a)) :=
  (hx.map T).tendsto_of_totallyBounded
    (totallyBounded_image_of_uniform_approximation T V hTV x happrox)

theorem isDunfordPettis_of_compact_restriction [CompleteSpace F]
    (T : E →L[𝕜] F) (V : G →L[𝕜] E)
    (hTV : IsCompactOperator (T.comp V))
    (happrox : ∀ (x : ℕ → E) (a : E), WeaklyConverges 𝕜 E x a →
      HasUniformBoundedApproximations V x) : IsDunfordPettis T :=
  fun x a hx => weaklyConverges_image_of_compact_restriction T V hTV hx (happrox x a hx)

end PL1
