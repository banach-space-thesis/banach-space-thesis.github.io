import BanachIsometric.LipschitzCycleStraightening

/-! A Lipschitz neighborhood retract has the same rational cycle classes
whether chains are required to be continuous or Lipschitz. The proofs use
an open cover by actual convex balls in the retraction domain. -/

noncomputable section
namespace BanachIsometric.SingularPrism.LipschitzNeighborhoodRetraction

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E} (D : LipschitzNeighborhoodRetraction s)

theorem exists_convex_open_cover :
    ∃ V : s → Set E, (∀ i, Convex ℝ (V i)) ∧ (∀ i, V i ⊆ D.domain) ∧
      (∀ i, IsOpen (convexCoverInSubtype s V i)) ∧
      ∀ x : s, ∃ i, x ∈ convexCoverInSubtype s V i := by
  have hr (x : s) : ∃ r : ℝ, 0 < r ∧ ball x.val r ⊆ D.domain :=
    Metric.isOpen_iff.mp D.isOpen_domain x.val (D.subset_domain x.property)
  choose r hrpos hrsub using hr
  refine ⟨fun x => ball x.val (r x), fun x => convex_ball _ _, hrsub, ?_, ?_⟩
  · intro i
    exact isOpen_ball.preimage continuous_subtype_val
  · intro x
    exact ⟨x, mem_ball_self (hrpos x)⟩

include D

theorem exists_lipschitz_cycle_representative (n : ℕ)
    (c : RawRationalChains s (n + 1)) (hc : rawBoundary n c = 0) :
    ∃ d : RawRationalChains s (n + 1), d ∈ rawLipschitzCarrier s (n + 1) ∧
      rawBoundary n d = 0 ∧
        ∃ a : RawRationalChains s (n + 2), rawBoundary (n + 1) a = c - d := by
  obtain ⟨V, hConvex, hDomain, hOpen, hCover⟩ := D.exists_convex_open_cover
  exact D.exists_lipschitz_cycle_representative_of_cover V hConvex hDomain hOpen hCover n c hc

theorem exists_lipschitz_boundary_filling (n : ℕ)
    (c : RawRationalChains s (n + 1)) (hc : c ∈ rawLipschitzCarrier s (n + 1))
    (a : RawRationalChains s (n + 2)) (ha : rawBoundary (n + 1) a = c) :
    ∃ b : RawRationalChains s (n + 2), b ∈ rawLipschitzCarrier s (n + 2) ∧
      rawBoundary (n + 1) b = c := by
  obtain ⟨V, hConvex, hDomain, hOpen, hCover⟩ := D.exists_convex_open_cover
  exact D.exists_lipschitz_boundary_filling_of_cover V hConvex hDomain hOpen hCover n c hc a ha

theorem exists_lipschitz_zero_boundary_filling
    (c : RawRationalChains s 0) (a : RawRationalChains s 1) (ha : rawBoundary 0 a = c) :
    ∃ b : RawRationalChains s 1, b ∈ rawLipschitzCarrier s 1 ∧ rawBoundary 0 b = c := by
  obtain ⟨V, hConvex, hDomain, hOpen, hCover⟩ := D.exists_convex_open_cover
  exact D.exists_lipschitz_zero_boundary_filling_of_cover V hConvex hDomain hOpen hCover c a ha

end BanachIsometric.SingularPrism.LipschitzNeighborhoodRetraction
