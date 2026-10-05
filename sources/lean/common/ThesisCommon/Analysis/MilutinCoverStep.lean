import ThesisCommon.Analysis.MilutinSmallCover
import Mathlib.Topology.MetricSpace.Gluing

/-! A single concrete refinement step for Ditor's inverse system: a finite
disjoint union of small compact sets, with a compatible metric, a regular
averaging projection, and two distinct lifts of each target point. -/

noncomputable section
namespace ThesisCommon
open Set

structure MilutinCoverStep (K : Type*) [MetricSpace K] (ε : ℝ) where
  count : ℕ
  count_ge_two : 2 ≤ count
  piece : Fin count → Set K
  compact : ∀ i, IsCompact (piece i)
  nonempty : ∀ i, (piece i).Nonempty
  small : ∀ i, Metric.diam (piece i) < ε
  cover : ∀ x : K, ∃ i, x ∈ interior (piece i)
  double : ∀ x : K, ∃ i j, i ≠ j ∧ x ∈ piece i ∧ x ∈ piece j

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] {ε : ℝ}

def milutinCoverStep (hε : 0 < ε) : MilutinCoverStep K ε := by
  apply Classical.choice
  obtain ⟨n, s, hn, hs, hc, hd⟩ := milutin_small_compact_cover (K := K) ε hε
  exact ⟨⟨n, hn, s, fun i => (hs i).1, fun i => (hs i).2.1,
    fun i => (hs i).2.2, hc, hd⟩⟩

namespace MilutinCoverStep
variable (S : MilutinCoverStep K ε)

abbrev Space := Σ i, S.piece i

instance pieceCompactSpace (i : Fin S.count) : CompactSpace (S.piece i) :=
  isCompact_iff_compactSpace.mp (S.compact i)

instance spaceMetricSpace : MetricSpace S.Space := Metric.Sigma.metricSpace

instance spaceCompactSpace : CompactSpace S.Space := inferInstanceAs (CompactSpace (Σ i, S.piece i))

instance spaceNonempty : Nonempty S.Space := by
  obtain ⟨x⟩ := ‹Nonempty K›
  obtain ⟨i, hi⟩ := S.cover x
  exact ⟨⟨i, ⟨x, interior_subset hi⟩⟩⟩

def projection : C(S.Space, K) := milutinCoverMap S.piece

@[simp] theorem projection_apply (x : S.Space) : S.projection x = x.2.val := rfl

theorem projection_surjective : Function.Surjective S.projection := by
  intro x
  obtain ⟨i, hi⟩ := S.cover x
  exact ⟨⟨i, ⟨x, interior_subset hi⟩⟩, rfl⟩

theorem projection_double (x : K) :
    ∃ y z : S.Space, y ≠ z ∧ S.projection y = x ∧ S.projection z = x := by
  obtain ⟨i, j, hij, hi, hj⟩ := S.double x
  refine ⟨⟨i, ⟨x, hi⟩⟩, ⟨j, ⟨x, hj⟩⟩, ?_, rfl, rfl⟩
  intro heq
  exact hij (congrArg Sigma.fst heq)

theorem projection_regular_averaging {𝕜 : Type*} [RCLike 𝕜] :
    ∃ A : C(S.Space, 𝕜) →L[𝕜] C(K, 𝕜),
      ‖A‖ = 1 ∧ A.comp (continuousMapPullback S.projection) =
        ContinuousLinearMap.id 𝕜 C(K, 𝕜) :=
  (milutin_finite_cover_regular_averaging S.piece S.cover).2

theorem dist_same_piece (i : Fin S.count) (x y : S.piece i) :
    dist (⟨i, x⟩ : S.Space) ⟨i, y⟩ = dist (x : K) (y : K) := by
  exact Metric.Sigma.dist_same (E := fun i => S.piece i) i x y

theorem same_piece_of_dist_lt_one (x y : S.Space) (h : dist x y < 1) : x.1 = y.1 :=
  Metric.Sigma.fst_eq_of_dist_lt_one x y h

end MilutinCoverStep
end ThesisCommon
