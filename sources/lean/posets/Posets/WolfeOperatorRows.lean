import Posets.WolfeDirac
import Posets.SzlenkOperator
import JLMS.AtomicOperatorMatrix

/-! Wolfe-rank lower bounds for actual arbitrary operator rows. A diagonal
lower bound on a closed set supplies the required mass in every neighborhood.
This is a proved input to preservation; it is not the preservation criterion. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u
namespace Posets

section Topological
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

local instance wolfeOperatorRowsDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeOperatorRowsDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfeMass_coordinate_le (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {x : K} {U : Set K} (hx : x ∈ U) :
    ‖M.representation (WeakDual.toStrongDual μ) x‖ ≤ wolfeMass M μ U := by
  rw [wolfeMass, JLMS.atomicRestriction_norm]
  have h := lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
    (JLMS.restrictionL1 U (M.representation (WeakDual.toStrongDual μ))) x
  simpa [hx] using h

def wolfeOperatorRow (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (x : K) :
    WeakDual 𝕜 (JLMS.CZero 𝕜 K) :=
  StrongDual.toWeakDual ((JLMS.evaluation x).comp T)

theorem wolfeOperatorRow_continuous
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) : Continuous (wolfeOperatorRow T) :=
  WeakDual.continuous_of_continuous_eval fun f => (T f).continuous

theorem wolfeOperatorRow_mem_adjointUnitBall
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (x : K) :
    wolfeOperatorRow T x ∈ adjointUnitBall T := by
  refine ⟨wolfeDirac x, ?_, rfl⟩
  change JLMS.evaluation (𝕜 := 𝕜) x ∈ Metric.closedBall 0 1
  simpa only [Metric.mem_closedBall, dist_zero_right] using JLMS.norm_evaluation_le (𝕜 := 𝕜) x

end Topological

section Metric
variable {𝕜 K : Type*} [RCLike 𝕜] [MetricSpace K] [Countable K]

theorem wolfeRows_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : K → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {A : Set K} (hA : IsClosed A) {ε : ℝ}
    (hmass : ∀ x ∈ A, ∀ U : Set K, IsOpen U → x ∈ U → ε ≤ wolfeMass M (μ x) U)
    (α : Ordinal.{u}) (hc : α.card ≤ Cardinal.aleph0) :
    ∀ x ∈ ordinalDerived A α, ∀ U : Set K, IsOpen U → x ∈ U →
      (μ x, U) ∈ wolfeFamily M ε (μ '' A) α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro x hx U hU hxU
      have hxA : x ∈ A := by simpa using hx
      rw [wolfeFamily_zero]
      exact ⟨⟨x, hxA, rfl⟩, hU, hmass x hxA U hU hxU⟩
  | succ α ih =>
      intro x hx U hU hxU
      have hαc : α.card ≤ Cardinal.aleph0 := (Ordinal.card_le_card (le_succ α)).trans hc
      have hxA : x ∈ A := by
        simpa using ordinalDerived_antitone hA (show 0 ≤ succ α from bot_le) hx
      obtain ⟨y, V, hy, hdisj, hconv, hclosure⟩ := exists_disjoint_open_point_sequence_closure
        (fun _ => ordinalDerived A α) (fun _ => by simpa only [ordinalDerived_succ] using hx)
        hU hxU
      refine (mem_wolfeFamily_succ M ε (μ '' A) α _).mpr
        ⟨⟨⟨x, hxA, rfl⟩, hU, hmass x hxA U hU hxU⟩, (fun n => (μ (y n), V n)), ?_, ?_⟩
      · intro n
        exact ih hαc (y n) (hy n).1 (V n) (hy n).2.2.1 (hy n).2.1
      · exact ⟨hμ.continuousAt.tendsto.comp hconv, hdisj, hclosure⟩
  | limit α hα ih =>
      intro x hx U hU hxU
      have hxA : x ∈ A := by
        simpa using ordinalDerived_antitone hA (show 0 ≤ α from bot_le) hx
      obtain ⟨a, ha, hcof⟩ := countable_limit_exists_strictMono_cofinal hα hc
      have hacc (n : ℕ) : x ∈ derivedSet (ordinalDerived A (a n).val) := by
        rw [← ordinalDerived_succ]
        exact ordinalDerived_antitone hA (hα.succ_lt (a n).property).le hx
      obtain ⟨y, V, hy, hdisj, hconv, hclosure⟩ := exists_disjoint_open_point_sequence_closure
        (fun n => ordinalDerived A (a n).val) hacc hU hxU
      refine (mem_wolfeFamily_limit M ε (μ '' A) hα _).mpr
        ⟨⟨⟨x, hxA, rfl⟩, hU, hmass x hxA U hU hxU⟩, a, ha, hcof,
          (fun n => (μ (y n), V n)), ?_, ?_⟩
      · intro n
        exact ih (a n).val (a n).property ((Ordinal.card_le_card (a n).property.le).trans hc)
          (y n) (hy n).1 (V n) (hy n).2.2.1 (hy n).2.1
      · exact ⟨hμ.continuousAt.tendsto.comp hconv, hdisj, hclosure⟩

theorem wolfeOperatorRows_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    {A : Set K} (hA : IsClosed A) {ε : ℝ}
    (hdiag : ∀ x ∈ A, ε ≤ ‖JLMS.atomicOperatorMatrix M T x x‖)
    (α : Ordinal.{u}) (hc : α.card ≤ Cardinal.aleph0) :
    ∀ x ∈ ordinalDerived A α, ∀ U : Set K, IsOpen U → x ∈ U →
      (wolfeOperatorRow T x, U) ∈ wolfeFamily M ε (adjointUnitBall T) α := by
  have hmass : ∀ x ∈ A, ∀ U : Set K, IsOpen U → x ∈ U →
      ε ≤ wolfeMass M (wolfeOperatorRow T x) U := by
    intro x hx U _ hxU
    exact (hdiag x hx).trans (wolfeMass_coordinate_le M (wolfeOperatorRow T x) hxU)
  intro x hx U hU hxU
  apply wolfeFamily_mono M le_rfl (α := α) (B := wolfeOperatorRow T '' A)
    (fun ν hν => ?_)
    (wolfeRows_ordinalDerived M (wolfeOperatorRow T) (wolfeOperatorRow_continuous T)
      hA hmass α hc x hx U hU hxU)
  obtain ⟨y, _, rfl⟩ := hν
  exact wolfeOperatorRow_mem_adjointUnitBall T y

theorem wolfeOperatorFamily_nonempty_of_diagonal (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    {A : Set K} (hA : IsClosed A) {ε : ℝ}
    (hdiag : ∀ x ∈ A, ε ≤ ‖JLMS.atomicOperatorMatrix M T x x‖)
    {α : Ordinal.{u}} (hc : α.card ≤ Cardinal.aleph0)
    (hne : (ordinalDerived A α).Nonempty) :
    (wolfeFamily M ε (adjointUnitBall T) α).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨(wolfeOperatorRow T x, univ),
    wolfeOperatorRows_ordinalDerived M T hA hdiag α hc x hx univ isOpen_univ (mem_univ _)⟩

end Metric
end Posets
