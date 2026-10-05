import Posets.AlspachCounterexampleGraftSpine
import JLMS.PointDifferenceEvaluation

/-! Continuous functions on a compact graft have uniformly small deviations
from their base values outside finitely many spines. Conversely, families
vanishing at their distinguished endpoints assemble to C₀ functions on the
punctured disjoint sum. These facts control continuity of the recursive rows. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology Filter
open scoped OnePoint
namespace Posets
variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K]
  (anchor : I → K) (X : I → Type*) [∀ i, TopologicalSpace (X i)]

theorem alspachGraft_vanishing_level_compact [CompactSpace K] [T2Space K]
    (g : AlspachGraft anchor X → 𝕜) (hg : Continuous g)
    (hbase : ∀ k, g (alspachGraftBase anchor X k) = 0) {ε : ℝ} (hε : 0 < ε) :
    IsCompact {z : Σ i, X i | ε ≤ ‖g (alspachGraftSpine anchor X z)‖} := by
  rw [(alspachGraftSpine_isOpenEmbedding anchor X).isEmbedding.isCompact_iff]
  have he : alspachGraftSpine anchor X ''
      {z : Σ i, X i | ε ≤ ‖g (alspachGraftSpine anchor X z)‖} =
      {p : AlspachGraft anchor X | ε ≤ ‖g p‖} := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hp
      rcases alspachGraft_cases anchor X p with ⟨k, rfl⟩ | ⟨z, rfl⟩
      · simp only [mem_setOf_eq, hbase, norm_zero] at hp
        exact (not_le_of_gt hε hp).elim
      · exact ⟨z, hp, rfl⟩
  rw [he]
  exact (isClosed_le continuous_const hg.norm).isCompact

theorem alspachGraft_finitely_many_large_spines [CompactSpace K] [T2Space K]
    (g : AlspachGraft anchor X → 𝕜) (hg : Continuous g)
    (hbase : ∀ k, g (alspachGraftBase anchor X k) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset I, ∀ i ∉ s, ∀ x : X i,
      ‖g (alspachGraftSpine anchor X ⟨i, x⟩)‖ < ε := by
  obtain ⟨s, t, hs, _, he⟩ := IsCompact.sigma_exists_finite_sigma_eq _
    (alspachGraft_vanishing_level_compact anchor X g hg hbase hε)
  refine ⟨hs.toFinset, ?_⟩
  intro i hi x
  by_contra hn
  have hm : (⟨i, x⟩ : Σ i, X i) ∈ {z | ε ≤ ‖g (alspachGraftSpine anchor X z)‖} :=
    le_of_not_gt hn
  rw [← he] at hm
  exact hi (hs.mem_toFinset.mpr hm.1)

def alspachCZeroOfCompactLevels {Y : Type*} [TopologicalSpace Y]
    (g : Y → 𝕜) (hg : Continuous g)
    (hlevel : ∀ ε : ℝ, 0 < ε → IsCompact {y | ε ≤ ‖g y‖}) : JLMS.CZero 𝕜 Y where
  toFun := g
  continuous_toFun := hg
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(hlevel ε hε).compl_mem_cocompact] with y hy
    simpa only [mem_compl_iff, mem_setOf_eq, not_le, dist_zero_right] using hy

variable {A : I → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]

theorem alspach_punctured_level_compact (p : ∀ i, A i) (g : ∀ i, A i → 𝕜)
    (hg : ∀ i, Continuous (g i)) (hroot : ∀ i, g i (p i) = 0)
    (i : I) {ε : ℝ} (hε : 0 < ε) :
    IsCompact {x : {x : A i // x ≠ p i} | ε ≤ ‖g i x‖} := by
  rw [Subtype.isCompact_iff]
  have he : Subtype.val '' {x : {x : A i // x ≠ p i} | ε ≤ ‖g i x‖} =
      {x : A i | ε ≤ ‖g i x‖} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx
      have hn : x ≠ p i := by
        intro h; subst x
        simpa only [mem_setOf_eq, hroot, norm_zero, not_le.mpr hε] using hx
      exact ⟨⟨x, hn⟩, hx, rfl⟩
  rw [he]
  exact (isClosed_le continuous_const (hg i).norm).isCompact

def alspachPuncturedSumCZero (p : ∀ i, A i) (g : ∀ i, A i → 𝕜)
    (hg : ∀ i, Continuous (g i)) (hroot : ∀ i, g i (p i) = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ s : Finset I, ∀ i ∉ s, ∀ x, ‖g i x‖ ≤ ε) :
    JLMS.CZero 𝕜 (Σ i, {x : A i // x ≠ p i}) :=
  alspachCZeroOfCompactLevels (fun z => g z.1 z.2)
    (continuous_sigma fun i => (hg i).comp continuous_subtype_val) (by
      intro ε hε
      obtain ⟨s, hs⟩ := hsmall (ε / 2) (half_pos hε)
      let t (i : I) := {x : {x : A i // x ≠ p i} | ε ≤ ‖g i x‖}
      have he : (s : Set I).sigma t =
          {z : Σ i, {x : A i // x ≠ p i} | ε ≤ ‖g z.1 z.2‖} := by
        ext z
        constructor
        · intro hz; exact hz.2
        · intro hz
          refine ⟨?_, hz⟩
          by_contra hi
          have hh := hs z.1 hi z.2
          change ε ≤ ‖g z.1 z.2‖ at hz
          linarith
      rw [← he]
      exact Set.isCompact_sigma s.finite_toSet (fun i _ =>
        alspach_punctured_level_compact p g hg hroot i hε))

end Posets

