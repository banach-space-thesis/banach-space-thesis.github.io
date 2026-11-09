import BanachIsometric.SphereRepetitionLocalLipschitz
import BanachIsometric.FiniteLipschitzNeighborhood

/-! The actual non-pole fiber of the raw sphere repetition has one compact
neighborhood on which the actual map is Lipschitz. This supplies the proved
geometric input of exact relative Lipschitz sphere approximation. -/

noncomputable section
namespace BanachIsometric.SphereGenerator
open Set Metric
open scoped Topology NNReal

theorem exists_compact_lipschitzOn_sphereRepetition_fiber_neighborhood
    (n d : ℕ) (target : Sph (n + 1)) (htarget : target ≠ sphereBasepoint (n + 1)) :
    ∃ A : Set (Sph (n + 1)), IsCompact A ∧
      (∀ w, sphereRepetition n d w = target → w ∈ interior A) ∧
      ∃ L : ℝ≥0, LipschitzOnWith L (sphereRepetition n d) A := by
  classical
  letI : CompactSpace (Sph (n + 1)) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin ((n + 1) + 1))) 1)
  let fiber : Set (Sph (n + 1)) := {w | sphereRepetition n d w = target}
  letI : Finite fiber := finite_sphereRepetition_fiber n d target htarget
  let s : Finset (Sph (n + 1)) := fiber.toFinite.toFinset
  have hs (w : Sph (n + 1)) : w ∈ s ↔ sphereRepetition n d w = target :=
    fiber.toFinite.mem_toFinset
  obtain ⟨A, hAc, hAinside, L, hL⟩ := exists_compact_lipschitzOn_neighborhood_of_finite
    (sphereRepetition n d) s (fun w hw =>
      exists_lipschitzOn_sphereRepetition_nhds_of_nonpole_fiber n d target w htarget ((hs w).mp hw))
  exact ⟨A, hAc, fun w hw => hAinside w ((hs w).mpr hw), L, hL⟩

end BanachIsometric.SphereGenerator
