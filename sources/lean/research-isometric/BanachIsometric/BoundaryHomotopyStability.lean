import BanachIsometric.MollifiedBoundary

/-!
# Local boundary stability of an actual continuous homotopy

Compactness and joint continuity supply one parameter neighbourhood which
works for every boundary point. Every affine segment between a nearby slice
and the reference slice then avoids the same closed target set.
-/

namespace BanachIsometric

open Set Metric Filter
open scoped Topology

variable {P X F : Type*} [PseudoMetricSpace P] [CompactSpace P]
  [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem realAffine_self (t : ℝ) (v : F) : realAffine t v v = v := by
  rw [realAffine, ← add_smul]
  have ht : (1 - t) + t = 1 := by ring
  rw [ht, one_smul]

theorem eventually_affine_boundary_avoids_closed
    (H : P → X → F) {b : Set X} (hb : IsCompact b)
    (hH : Continuous (fun z : P × b => H z.1 z.2))
    {T : Set F} (hT : IsClosed T) (p : P)
    (hp : ∀ x ∈ b, H p x ∉ T) :
    ∀ᶠ q in 𝓝 p, ∀ x ∈ b, ∀ t : unitInterval,
      realAffine t (H q x) (H p x) ∉ T := by
  letI : CompactSpace b := isCompact_iff_compactSpace.mp hb
  let Fp : b → F := fun x => H p x
  have hFp : Continuous Fp := hH.comp (continuous_const.prodMk continuous_id)
  have hK : IsCompact (Set.range Fp) := isCompact_range hFp
  have hsub : Set.range Fp ⊆ Tᶜ := by
    rintro _ ⟨x, rfl⟩
    exact hp x x.property
  obtain ⟨ε, hε, hthick⟩ := hK.exists_thickening_subset_open hT.isOpen_compl hsub
  obtain ⟨δ, hδ, hδH⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hH) ε hε
  filter_upwards [ball_mem_nhds p hδ] with q hq
  intro x hx t
  apply hthick
  apply mem_thickening_iff.mpr
  refine ⟨Fp ⟨x, hx⟩, mem_range_self _, ?_⟩
  have hpair : dist (q, (⟨x, hx⟩ : b)) (p, (⟨x, hx⟩ : b)) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hq
  have hclose : dist (H q x) (H p x) < ε := hδH hpair
  have ha := dist_realAffine_le_add t (H q x) (H p x) (H p x) (H p x)
  rw [realAffine_self, dist_self, add_zero] at ha
  exact ha.trans_lt hclose

end BanachIsometric
