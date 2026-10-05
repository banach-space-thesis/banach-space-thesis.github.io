import Posets.WolfeFamilies
import Posets.WolfePointSequences

/-! Exact lower bounds for Wolfe families of point evaluations. The proof uses
actual disjoint neighborhoods at successors and explicit countable cofinal
sequences at limits. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u
namespace Posets

theorem countable_limit_exists_strictMono_cofinal {α : Ordinal.{u}}
    (hα : IsSuccLimit α) (hc : α.card ≤ Cardinal.aleph0) :
    ∃ a : ℕ → Iio α, StrictMono (fun n => (a n).val) ∧
      ∀ β < α, ∃ n, β ≤ (a n).val := by
  classical
  haveI : Countable (Iio α) := Cardinal.mk_le_aleph0_iff.mp (by
    rw [Ordinal.mk_Iio_ordinal]
    exact Cardinal.lift_le_aleph0.mpr hc)
  haveI : Nonempty (Iio α) := ⟨⟨0, hα.bot_lt⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Iio α)
  let a : ℕ → Iio α := Nat.rec (e 0) (fun n prev =>
    ⟨max (succ prev.val) (e (n + 1)).val,
      max_lt (hα.succ_lt prev.property) (e (n + 1)).property⟩)
  refine ⟨a, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    exact (lt_succ (a n).val).trans_le (le_max_left _ _)
  · intro β hβ
    obtain ⟨n, hn⟩ := he ⟨β, hβ⟩
    refine ⟨n, ?_⟩
    have hea : (e n).val ≤ (a n).val := by
      cases n with
      | zero => exact le_rfl
      | succ n => exact le_max_right _ _
    simpa only [hn] using hea

section Topological
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

def wolfeDirac (x : K) : WeakDual 𝕜 (JLMS.CZero 𝕜 K) :=
  StrongDual.toWeakDual (JLMS.evaluation x)

theorem wolfeDirac_continuous : Continuous (wolfeDirac (𝕜 := 𝕜) (K := K)) :=
  WeakDual.continuous_of_continuous_eval fun f => f.continuous

theorem wolfeMass_dirac (M : JLMS.AtomicDualModel 𝕜 K) {x : K} {U : Set K}
    (hx : x ∈ U) : wolfeMass M (wolfeDirac x) U = 1 := by
  classical
  have hc : M.representation (JLMS.evaluation x) = lp.single 1 x (1 : 𝕜) := by
    rw [← M.pointMass x, M.representation.apply_symm_apply]
  change ‖JLMS.atomicRestriction M U (JLMS.evaluation x)‖ = 1
  rw [JLMS.atomicRestriction_norm, hc]
  have hres : JLMS.restrictionL1 U (lp.single 1 x (1 : 𝕜)) = lp.single 1 x (1 : 𝕜) := by
    ext y
    by_cases hy : y = x
    · subst y; simp [hx]
    · simp [JLMS.restrictL1_apply, hy]
  rw [hres, lp.norm_single (by norm_num : (0 : ENNReal) < 1), norm_one]

end Topological

section Metric
variable {𝕜 K : Type*} [RCLike 𝕜] [MetricSpace K] [Countable K]

/-- Every point at Cantor--Bendixson level α gives a Wolfe node at level α,
in every prescribed open neighborhood, with its full unit point-mass. -/
theorem wolfeDirac_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    {A : Set K} (hA : IsClosed A) {ε : ℝ} (hε : ε ≤ 1) (α : Ordinal.{u})
    (hc : α.card ≤ Cardinal.aleph0) :
    ∀ x ∈ ordinalDerived A α, ∀ U : Set K, IsOpen U → x ∈ U →
      (wolfeDirac (𝕜 := 𝕜) x, U) ∈ wolfeFamily M ε (wolfeDirac '' A) α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro x hx U hU hxU
      rw [wolfeFamily_zero]
      exact ⟨⟨x, by simpa using hx, rfl⟩, hU, by rwa [wolfeMass_dirac M hxU]⟩
  | succ α ih =>
      intro x hx U hU hxU
      have hαc : α.card ≤ Cardinal.aleph0 := (Ordinal.card_le_card (le_succ α)).trans hc
      obtain ⟨y, V, hy, hdisj, hconv, hclosure⟩ := exists_disjoint_open_point_sequence_closure
        (fun _ => ordinalDerived A α) (fun _ => by simpa only [ordinalDerived_succ] using hx)
        hU hxU
      refine (mem_wolfeFamily_succ M ε (wolfeDirac '' A) α _).mpr ⟨?_,
        (fun n => (wolfeDirac (y n), V n)), ?_, ?_⟩
      · have hxA : x ∈ A := by
          simpa using ordinalDerived_antitone hA (show 0 ≤ succ α from bot_le) hx
        exact ⟨⟨x, hxA, rfl⟩, hU, by rwa [wolfeMass_dirac M hxU]⟩
      · intro n
        exact ih hαc (y n) (hy n).1 (V n) (hy n).2.2.1 (hy n).2.1
      · exact ⟨wolfeDirac_continuous.continuousAt.tendsto.comp hconv,
          hdisj, hclosure⟩
  | limit α hα ih =>
      intro x hx U hU hxU
      obtain ⟨a, ha, hcof⟩ := countable_limit_exists_strictMono_cofinal hα hc
      have hacc (n : ℕ) : x ∈ derivedSet (ordinalDerived A (a n).val) := by
        rw [← ordinalDerived_succ]
        exact ordinalDerived_antitone hA (hα.succ_lt (a n).property).le hx
      obtain ⟨y, V, hy, hdisj, hconv, hclosure⟩ := exists_disjoint_open_point_sequence_closure
        (fun n => ordinalDerived A (a n).val) hacc hU hxU
      refine (mem_wolfeFamily_limit M ε (wolfeDirac '' A) hα _).mpr
        ⟨?_, a, ha, hcof, (fun n => (wolfeDirac (y n), V n)), ?_, ?_⟩
      · have hxA : x ∈ A := by
          simpa using ordinalDerived_antitone hA (show 0 ≤ α from bot_le) hx
        exact ⟨⟨x, hxA, rfl⟩, hU, by rwa [wolfeMass_dirac M hxU]⟩
      · intro n
        exact ih (a n).val (a n).property ((Ordinal.card_le_card (a n).property.le).trans hc)
          (y n) (hy n).1 (V n) (hy n).2.2.1 (hy n).2.1
      · exact ⟨wolfeDirac_continuous.continuousAt.tendsto.comp hconv,
          hdisj, hclosure⟩

end Metric
end Posets
