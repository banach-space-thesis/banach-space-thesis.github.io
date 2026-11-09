import PL1.SchurLattice
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weak compactness in separable Schur spaces

These lemmas prove the norm-compactness consequence of weak compactness,
without assuming that the continuous dual is separable. Weak compactness of
order intervals is a separate premise in the lattice corollary below.
-/

noncomputable section
open Filter TopologicalSpace
open scoped Topology

namespace PL1.SchurLattice

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeparableSpace E]

/-- Hahn--Banach applied to a norm-dense sequence gives a countable family
of continuous functionals separating every pair of points. The dual space
itself need not be separable. -/
theorem exists_countable_separating_dual :
    ∃ g : ℕ → E →L[𝕜] 𝕜, (∀ n, ‖g n‖ ≤ 1) ∧
      ∀ ⦃x y : E⦄, x ≠ y → ∃ n, g n x ≠ g n y := by
  classical
  choose g hg hgn using fun n => exists_dual_vector'' 𝕜 (denseSeq E n)
  refine ⟨g, hg, ?_⟩
  intro x y hxy
  by_contra hbad
  push Not at hbad
  let z := x - y
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy
  have hgz (n : ℕ) : g n z = 0 := by simp [z, hbad n]
  obtain ⟨n, hn⟩ := (denseRange_denseSeq E).exists_dist_lt z
    (show 0 < ‖z‖ / 3 from div_pos (norm_pos_iff.mpr hz) (by norm_num))
  have hdist : ‖z - denseSeq E n‖ < ‖z‖ / 3 := by simpa [dist_eq_norm] using hn
  have hgnorm : ‖denseSeq E n‖ ≤ ‖z - denseSeq E n‖ := by
    have hb := (g n).le_opNorm (z - denseSeq E n)
    rw [map_sub, hgz, hgn] at hb
    simpa using hb.trans (mul_le_of_le_one_left (norm_nonneg _) (hg n))
  have hzbound : ‖z‖ ≤ ‖z - denseSeq E n‖ + ‖denseSeq E n‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - denseSeq E n) (denseSeq E n)
  linarith [norm_nonneg z]

/-- Every weakly compact subset of a separable normed space is metrizable in
its weak topology. This is restricted to compact subsets. -/
theorem weak_metrizable_of_isCompact (K : Set (WeakSpace 𝕜 E))
    (hK : IsCompact K) : MetrizableSpace K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨g, _, hsep⟩ := exists_countable_separating_dual (𝕜 := 𝕜) (E := E)
  apply Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun n (x : K) => g n ((toWeakSpace 𝕜 E).symm x.val))
  · intro n
    exact (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (g n)).comp
      continuous_subtype_val
  · intro x y hxy
    exact hsep (fun h => hxy (Subtype.ext ((toWeakSpace 𝕜 E).symm.injective h)))

/-- Weak compactness implies weak sequential compactness for subsets of a
separable normed space; no general Eberlein--Smulian theorem is used. -/
theorem weak_isSeqCompact_of_isCompact (K : Set (WeakSpace 𝕜 E))
    (hK : IsCompact K) : IsSeqCompact K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MetrizableSpace K := weak_metrizable_of_isCompact K hK
  simpa using IsSeqCompact.range
    (continuous_iff_seqContinuous.mp (continuous_subtype_val : Continuous
      (fun x : K => (x : WeakSpace 𝕜 E))))

/-- A weakly compact set in a separable Schur space is compact for the
original norm topology. -/
theorem isCompact_of_weak_isCompact (hS : HasSchurProperty 𝕜 E)
    (s : Set E) (hs : IsCompact ((toWeakSpace 𝕜 E) '' s)) : IsCompact s := by
  apply IsSeqCompact.isCompact
  intro x hx
  obtain ⟨a, ha, φ, hφ, hlim⟩ := weak_isSeqCompact_of_isCompact _ hs
    (fun n => Set.mem_image_of_mem _ (hx n))
  obtain ⟨a, ha, rfl⟩ := ha
  refine ⟨a, ha, φ, hφ, hS _ _ ?_⟩
  intro g
  exact ((WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip g).tendsto _).comp hlim

/-- On subsets of a separable Schur space, weak compactness and norm
compactness agree. -/
theorem isCompact_iff_weak_isCompact (hS : HasSchurProperty 𝕜 E) (s : Set E) :
    IsCompact s ↔ IsCompact ((toWeakSpace 𝕜 E) '' s) :=
  ⟨fun hs => hs.image (toWeakSpaceCLM 𝕜 E).continuous,
    isCompact_of_weak_isCompact hS s⟩

end PL1.SchurLattice
