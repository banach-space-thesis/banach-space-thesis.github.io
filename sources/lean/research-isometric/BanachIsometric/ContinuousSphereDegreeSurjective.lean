import BanachIsometric.ContinuousSphereSignedDegree
import BanachIsometric.SphereSignedDegreeSurjective

/-!
# Nonzero degree of a continuous sphere map forces surjectivity

A missing target point has positive distance from the compact image. An
actual sufficiently close Lipschitz approximation still misses that point,
while computing the same proved degree. This contradicts the actual signed
count surjectivity theorem for Lipschitz maps.
-/

namespace BanachIsometric

open Set Metric
open scoped Topology NNReal

theorem continuousSphereSignedDegree_surjective_of_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hdegree : continuousSphereSignedDegree e f ≠ 0) : Function.Surjective f := by
  letI : CompactSpace (sphere (0 : V) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  intro u
  by_contra hmiss
  have hu : u ∉ range f := hmiss
  have hopen : IsOpen (range f)ᶜ := (isCompact_range f.continuous).isClosed.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen u hu
  let ε : ℝ := min (1 / 4) (δ / 2)
  have hε : 0 < ε := lt_min (by norm_num) (half_pos hδ)
  obtain ⟨g, L, hL, hclose⟩ := exists_lipschitz_sphere_approximation_on_compact
    (isCompact_sphere (0 : V) 1) f hε
  have hclose' : ∀ z, dist (g z) (f z) < (1 / 4 : ℝ) :=
    fun z => (hclose z).trans_le (min_le_left _ _)
  have hdeg : sphereSignedDegree e g ≠ 0 := by
    rwa [← continuousSphereSignedDegree_eq_of_lipschitz_approximation e f hL hclose']
  obtain ⟨x, hx⟩ := sphereSignedDegree_surjective_of_ne_zero e hL hdeg u
  have hdist : dist (f x) u < δ := by
    have hc := hclose x
    rw [hx, dist_comm] at hc
    have hεle : ε ≤ δ / 2 := min_le_right _ _
    linarith
  exact hball (mem_ball.mpr hdist) (mem_range_self x)

end BanachIsometric
