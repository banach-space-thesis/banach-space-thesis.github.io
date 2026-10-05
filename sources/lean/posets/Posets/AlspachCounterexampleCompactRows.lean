import Posets.AlspachCounterexampleLimitContinuity
import Posets.AlspachCounterexampleMetrizable

/-! Actual countable compact Hausdorff probability families, including every
finite stage and their ω limit. All continuity and lower estimates follow
from the preceding constructions, rather than being postulated. -/

noncomputable section
namespace Posets
universe u v
variable (𝕜 : Type v) [RCLike 𝕜]

structure AlspachCompactRows where
  Point : Type u
  Index : Type u
  [pointTopology : TopologicalSpace Point]
  [indexTopology : TopologicalSpace Index]
  [pointCompact : CompactSpace Point]
  [indexCompact : CompactSpace Index]
  [pointHausdorff : T2Space Point]
  [indexHausdorff : T2Space Index]
  [pointCountable : Countable Point]
  [indexCountable : Countable Index]
  rows : AlspachPointedRows 𝕜 Point Index
  continuousRows : rows.ContinuousRows

attribute [instance] AlspachCompactRows.pointTopology AlspachCompactRows.indexTopology
  AlspachCompactRows.pointCompact AlspachCompactRows.indexCompact
  AlspachCompactRows.pointHausdorff AlspachCompactRows.indexHausdorff
  AlspachCompactRows.pointCountable AlspachCompactRows.indexCountable

namespace AlspachCompactRows
variable {𝕜}

instance pointNonempty (F : AlspachCompactRows 𝕜) : Nonempty F.Point := ⟨F.rows.point⟩
instance indexNonempty (F : AlspachCompactRows 𝕜) : Nonempty F.Index := ⟨F.rows.index⟩

instance pointMetrizable (F : AlspachCompactRows 𝕜) : TopologicalSpace.MetrizableSpace F.Point :=
  alspach_countable_compact_metrizable _
instance indexMetrizable (F : AlspachCompactRows 𝕜) : TopologicalSpace.MetrizableSpace F.Index :=
  alspach_countable_compact_metrizable _

def base (B : Type u) [TopologicalSpace B] [CompactSpace B] [T2Space B] [Countable B]
    (p : B) : AlspachCompactRows.{u, v} 𝕜 where
  Point := B
  Index := B
  rows := AlspachPointedRows.base p
  continuousRows := by
    intro f
    have he (x : B) : ((AlspachPointedRows.base (𝕜 := 𝕜) p).row x).eval f =
        (1 / 2 : 𝕜) * (f x + f p) := by
      by_cases hx : x = p
      · subst x
        change (alspachBaseRow p p).eval f = _
        simp only [alspachBaseRow, ↓reduceIte, AlspachProbability.eval_point]
        ring
      · simp [AlspachPointedRows.base, alspachBaseRow, hx]
    simp_rw [he]
    exact continuous_const.mul (f.continuous.add continuous_const)

def successor (F G : AlspachCompactRows.{u, v} 𝕜) : AlspachCompactRows.{u, v} 𝕜 where
  Point := F.rows.SuccessorPointGraft G.rows
  Index := F.rows.SuccessorIndexGraft G.rows
  rows := F.rows.topologicalSuccessor G.rows
  continuousRows := F.rows.topologicalSuccessor_continuous G.rows F.continuousRows G.continuousRows

def limit (F : ℕ → AlspachCompactRows.{u, v} 𝕜) : AlspachCompactRows.{u, v} 𝕜 where
  Point := AlspachPointedRows.LimitPointSpace (fun n => (F n).rows)
  Index := AlspachPointedRows.LimitIndexSpace (fun n => (F n).rows)
  pointCountable := inferInstanceAs (Countable (AlspachPointedRows.LimitPoints (fun n => (F n).rows)))
  indexCountable := inferInstanceAs (Countable (AlspachPointedRows.LimitIndices (fun n => (F n).rows)))
  rows := AlspachPointedRows.topologicalLimit (fun n => (F n).rows)
  continuousRows := AlspachPointedRows.topologicalLimit_continuous (fun n => (F n).rows)
    (fun n => (F n).continuousRows)

end AlspachCompactRows

variable {𝕜}

def alspachFiniteCompactRows (B : Type u) [TopologicalSpace B] [CompactSpace B]
    [T2Space B] [Countable B] (p : B) : ℕ → AlspachCompactRows.{u, v} 𝕜
  | 0 => AlspachCompactRows.base B p
  | n + 1 => (AlspachCompactRows.base B p).successor (alspachFiniteCompactRows B p n)

def alspachOmegaCompactRows (B : Type u) [TopologicalSpace B] [CompactSpace B]
    [T2Space B] [Countable B] (p : B) : AlspachCompactRows.{u, v} 𝕜 :=
  AlspachCompactRows.limit (alspachFiniteCompactRows B p)

end Posets
