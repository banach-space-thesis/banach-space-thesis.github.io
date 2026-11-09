import BanachIsometric.RelativeSphereApproximation
import BanachIsometric.ContinuousSphereSignedDegree

/-!
# Actual Lipschitz approximation preserving a specified sphere fiber and its germs

The compact complement of a prescribed fiber neighborhood has an image
separated from the target. An actual sufficiently close relative Lipschitz
approximation therefore has exactly the same target fiber, and agrees on
neighborhoods of every point in that fiber.
-/

namespace BanachIsometric

open Set Metric Filter
open scoped Topology NNReal

theorem exists_lipschitz_sphere_approximation_preserving_fiber_germs
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : C(sphere (0 : V) 1, sphere (0 : V) 1)) (v : sphere (0 : V) 1)
    {A : Set (sphere (0 : V) 1)} (hA : IsCompact A) {K : ℝ≥0} (hfA : LipschitzOnWith K f A)
    (hfiber : ∀ x, f x = v → x ∈ interior A) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : C(sphere (0 : V) 1, sphere (0 : V) 1), ∃ L : ℝ≥0, LipschitzWith L G ∧
      (∀ x, dist (G x) (f x) < ε) ∧
      (∀ x, G x = v ↔ f x = v) ∧
      ∀ x, f x = v → (G : sphere (0 : V) 1 → sphere (0 : V) 1) =ᶠ[𝓝 x] f := by
  letI : CompactSpace (sphere (0 : V) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let B : Set (sphere (0 : V) 1) := (interior A)ᶜ
  have hB : IsCompact B := isOpen_interior.isClosed_compl.isCompact
  have hv : v ∉ f '' B := by
    rintro ⟨x, hx, hfx⟩
    exact hx (hfiber x hfx)
  have hopen : IsOpen (f '' B)ᶜ := (hB.image f.continuous).isClosed.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen v hv
  let η : ℝ := min ε (δ / 2)
  have hη : 0 < η := lt_min hε (half_pos hδ)
  obtain ⟨G, L, hL, hclose, hagree⟩ := exists_lipschitz_sphere_approximation_relative f hA hfA hη
  have hinside (x : sphere (0 : V) 1) (hx : G x = v) : x ∈ interior A := by
    by_contra hnot
    have hd : dist (f x) v < δ := by
      have hc := hclose x
      rw [hx, dist_comm] at hc
      have hηle : η ≤ δ / 2 := min_le_right _ _
      linarith
    exact hball (mem_ball.mpr hd) ⟨x, hnot, rfl⟩
  refine ⟨G, L, hL, (fun x => (hclose x).trans_le (min_le_left _ _)), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      exact (hagree (interior_subset (hinside x hx))).symm.trans hx
    · intro hx
      exact (hagree (interior_subset (hfiber x hx))).trans hx
  · intro x hx
    filter_upwards [isOpen_interior.mem_nhds (hfiber x hx)] with z hz
    exact hagree (interior_subset hz)

end BanachIsometric
