import Posets.WolfeMassBounds
import JLMS.OrdinalSupportBounds
import Mathlib.SetTheory.Cardinal.Regular

/-! A fixed atomic row touches only countably many disjoint cells. Outside
those cells the entire union has exactly zero variation mass. An ordinal
index of uncountable cofinality therefore has an exactly zero-mass tail.
These are support lemmas for future tree pruning, not a preservation theorem. -/

noncomputable section
open Set
universe u
namespace Posets
variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K]

def wolfeAtomicTouchedCells (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : I → Set K) : Set I :=
  {i | ∃ x ∈ U i, M.representation (WeakDual.toStrongDual μ) x ≠ 0}

theorem wolfeMass_eq_zero_of_coordinates (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {D : Set K}
    (hD : ∀ x ∈ D, M.representation (WeakDual.toStrongDual μ) x = 0) :
    wolfeMass M μ D = 0 := by
  classical
  rw [wolfeMass_eq_tsum]
  have he : (fun x => D.indicator
      (fun x => ‖M.representation (WeakDual.toStrongDual μ) x‖) x) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ D
    · rw [Set.indicator_of_mem hx, hD x hx, norm_zero]
    · rw [Set.indicator_of_notMem hx]
  rw [he, tsum_zero]

theorem wolfeAtomicTouchedCells_countable (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : I → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    (wolfeAtomicTouchedCells M μ U).Countable := by
  have hsmall (x : K) : {i | x ∈ U i}.Subsingleton := by
    intro i hi j hj
    by_contra hij
    exact Set.disjoint_left.mp (hU hij) hi hj
  have he : wolfeAtomicTouchedCells M μ U =
      ⋃ x ∈ Function.support (M.representation (WeakDual.toStrongDual μ)), {i | x ∈ U i} := by
    ext i
    simp only [wolfeAtomicTouchedCells, mem_setOf_eq, mem_iUnion, Function.mem_support]
    constructor
    · rintro ⟨x, hx, hn⟩
      exact ⟨x, hn, hx⟩
    · rintro ⟨x, hn, hx⟩
      exact ⟨x, hx, hn⟩
  rw [he]
  exact (JLMS.atomicDual_countable_support M (WeakDual.toStrongDual μ)).biUnion
    (fun x _ => (hsmall x).countable)

theorem wolfeMass_untouched_union_eq_zero (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : I → Set K) :
    wolfeMass M μ (⋃ i ∉ wolfeAtomicTouchedCells M μ U, U i) = 0 := by
  apply wolfeMass_eq_zero_of_coordinates M μ
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  by_contra hn
  exact hi ⟨x, hxi, hn⟩

theorem wolfeMass_exists_countable_disjoint_cell_support (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : I → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∃ J : Set I, J.Countable ∧ wolfeMass M μ (⋃ i ∉ J, U i) = 0 :=
  ⟨wolfeAtomicTouchedCells M μ U, wolfeAtomicTouchedCells_countable M μ U hU,
    wolfeMass_untouched_union_eq_zero M μ U⟩

theorem wolfeMass_exists_zero_ordinal_tail (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (U : Iio α → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∃ β < α, wolfeMass M μ (⋃ i : Iio α, ⋃ (_ : β < i.val), U i) = 0 := by
  let J := wolfeAtomicTouchedCells M μ U
  have hJ : J.Countable := wolfeAtomicTouchedCells_countable M μ U hU
  obtain ⟨β, hβ, hb⟩ := JLMS.exists_bound_countable_ordinals hα
    (hJ.image Subtype.val) (by rintro x ⟨i, _, rfl⟩; exact i.property)
  refine ⟨β, hβ, le_antisymm ?_ (wolfeMass_nonneg M μ _)⟩
  calc
    wolfeMass M μ (⋃ i : Iio α, ⋃ (_ : β < i.val), U i) ≤
        wolfeMass M μ (⋃ i ∉ J, U i) := by
      apply wolfeMass_mono M μ
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      refine mem_iUnion₂.mpr ⟨i, ?_, hxi⟩
      intro hij
      exact (not_le_of_gt hi) (hb i.val ⟨i, hij, rfl⟩)
    _ = 0 := wolfeMass_untouched_union_eq_zero M μ U

theorem wolfeMass_exists_zero_regular_tail (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (U : Iio c.ord → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∃ β < c.ord, wolfeMass M μ (⋃ i : Iio c.ord, ⋃ (_ : β < i.val), U i) = 0 :=
  wolfeMass_exists_zero_ordinal_tail M μ (by simpa only [hc.cof_eq] using hu) U hU

end Posets
