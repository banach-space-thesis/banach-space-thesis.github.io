import ThesisCommon.Analysis.CountableMetricClopen
import ThesisCommon.Analysis.CountableCompactRankBound
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! A concrete clopen-shell decomposition around any point of a countable
compact metric space. The space is the one-point compactification of the
topological sum of the compact shells. If the terminal derivative is a
singleton, every nonempty shell has strictly smaller Cantor--Bendixson rank. -/

noncomputable section
open Set Order Topology Filter
universe u
namespace ThesisCommon
variable {K : Type u} [MetricSpace K] [Countable K]

def countableClopenRadius (p : K) (n : ℕ) : ℝ :=
  (countableMetric_exists_clopen_ball p (show 0 < 1 / ((n : ℝ) + 1) by positivity)).choose

theorem countableClopenRadius_spec (p : K) (n : ℕ) :
    0 < countableClopenRadius p n ∧ countableClopenRadius p n < 1 / ((n : ℝ) + 1) ∧
      IsClopen (Metric.ball p (countableClopenRadius p n)) :=
  (countableMetric_exists_clopen_ball p (show 0 < 1 / ((n : ℝ) + 1) by positivity)).choose_spec

def countableClopenNest (p : K) : ℕ → Set K
  | 0 => univ
  | n + 1 => countableClopenNest p n ∩ Metric.ball p (countableClopenRadius p n)

theorem countableClopenNest_isClopen (p : K) (n : ℕ) : IsClopen (countableClopenNest p n) := by
  induction n with
  | zero => exact isClopen_univ
  | succ n ih => exact ih.inter (countableClopenRadius_spec p n).2.2

theorem countableClopenNest_mem (p : K) (n : ℕ) : p ∈ countableClopenNest p n := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih, Metric.mem_ball_self (countableClopenRadius_spec p n).1⟩

theorem countableClopenNest_antitone (p : K) : Antitone (countableClopenNest p) :=
  antitone_nat_of_succ_le fun _ => inter_subset_left

theorem countableClopenNest_only_point (p x : K) (hx : ∀ n, x ∈ countableClopenNest p n) :
    x = p := by
  have hbound (n : ℕ) : dist x p ≤ 1 / ((n : ℝ) + 1) := by
    have hball : dist x p < countableClopenRadius p n := (hx (n + 1)).2
    exact (hball.trans (countableClopenRadius_spec p n).2.1).le
  have hz : dist x p ≤ 0 := ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall hbound)
  exact dist_eq_zero.mp (le_antisymm hz dist_nonneg)

def countableClopenShell (p : K) (n : ℕ) : Set K :=
  countableClopenNest p n \ countableClopenNest p (n + 1)

theorem countableClopenShell_isClopen (p : K) (n : ℕ) : IsClopen (countableClopenShell p n) :=
  (countableClopenNest_isClopen p n).diff (countableClopenNest_isClopen p (n + 1))

theorem countableClopenShell_not_mem (p : K) (n : ℕ) : p ∉ countableClopenShell p n :=
  fun h => h.2 (countableClopenNest_mem p (n + 1))

theorem countableClopenShell_disjoint (p : K) :
    Pairwise (fun n m => Disjoint (countableClopenShell p n) (countableClopenShell p m)) := by
  intro n m hnm
  have hlt {i j : ℕ} (hij : i < j) : Disjoint (countableClopenShell p i) (countableClopenShell p j) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 (countableClopenNest_antitone p (Nat.succ_le_iff.mpr hij) hy.1)
  exact (lt_or_gt_of_ne hnm).elim hlt (fun h => (hlt h).symm)

theorem countableClopenShell_covers (p : K) {x : K} (hxp : x ≠ p) :
    ∃ n, x ∈ countableClopenShell p n := by
  classical
  have hex : ∃ n, x ∉ countableClopenNest p n := by
    by_contra! hx
    exact hxp (countableClopenNest_only_point p x hx)
  have hmin := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro he
    simp [he, countableClopenNest] at hmin
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨n, ?_, ?_⟩
  · have hprev := Nat.find_min hex (show n < Nat.find hex by omega)
    exact not_not.mp hprev
  · simpa [hn] using hmin

def countableClopenShellMap (p : K) : (Σ n, countableClopenShell p n) → K :=
  fun z => z.2.val

theorem countableClopenShellMap_injective (p : K) : Function.Injective (countableClopenShellMap p) := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  have hxy : x.val = y.val := h
  have hnm : n = m := by
    by_contra hnm
    exact Set.disjoint_left.mp (countableClopenShell_disjoint p hnm) x.property
      (hxy ▸ y.property)
  subst m
  congr 1
  exact Subtype.ext hxy

theorem countableClopenShellMap_isOpenEmbedding (p : K) :
    Topology.IsOpenEmbedding (countableClopenShellMap p) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_sigma fun _ => continuous_subtype_val
  · exact countableClopenShellMap_injective p
  · apply isOpenMap_sigma.mpr
    intro n
    exact (countableClopenShell_isClopen p n).isOpen.isOpenEmbedding_subtypeVal.isOpenMap

theorem countableClopenShellMap_range (p : K) : Set.range (countableClopenShellMap p) = {p}ᶜ := by
  ext x
  constructor
  · rintro ⟨⟨n, y⟩, rfl⟩ h
    have heq : y.val = p := h
    apply countableClopenShell_not_mem p n
    simpa only [heq] using y.property
  · intro hx
    obtain ⟨n, hn⟩ := countableClopenShell_covers p hx
    exact ⟨⟨n, x, hn⟩, rfl⟩

variable [CompactSpace K]

theorem countableCompactShell_isCompact (p : K) (n : ℕ) : IsCompact (countableClopenShell p n) :=
  (countableClopenShell_isClopen p n).isClosed.isCompact

instance countableCompactShell_compactSpace (p : K) (n : ℕ) :
    CompactSpace (countableClopenShell p n) :=
  isCompact_iff_compactSpace.mp (countableCompactShell_isCompact p n)

def countableCompactShellHomeomorph (p : K) :
    OnePoint (Σ n, countableClopenShell p n) ≃ₜ K :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p (countableClopenShellMap p)
    (countableClopenShellMap_isOpenEmbedding p).isEmbedding (countableClopenShellMap_range p)

theorem countableCompactShell_rank_lt (p : K) {α : Ordinal.{u}}
    (hα : ordinalDerived (univ : Set K) α = {p}) (n : ℕ)
    (hne : (countableClopenShell p n).Nonempty) :
    ∃ β < α, (ordinalDerived (countableClopenShell p n) β).Finite ∧
      (ordinalDerived (countableClopenShell p n) β).Nonempty ∧
      ordinalDerived (countableClopenShell p n) (succ β) = ∅ := by
  apply countableCompact_piece_rank_lt isCompact_univ
    (countableClopenShell_isClopen p n).isClosed.isCompact (subset_univ _) hne
  rw [hα, Set.disjoint_singleton_right]
  exact countableClopenShell_not_mem p n

end ThesisCommon
