import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.PiSystem

/-! A countable mutually singular family has actual pairwise disjoint measurable
supports. No finiteness, topology, or common dominating measure is required. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon

theorem exists_disjoint_measurable_supports_of_pairwise_mutuallySingular
    {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X)
    (h : Pairwise fun n m => (μ n).MutuallySingular (μ m)) :
    ∃ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) ∧
      Pairwise (fun n m => Disjoint (A n) (A m)) ∧
      (∀ n, μ n (A n)ᶜ = 0) ∧ (∀ n m, n ≠ m → μ n (A m) = 0) := by
  let B : ℕ → Set X := fun n => ⋂ m : {m : ℕ // m ≠ n}, (h m.property).nullSet
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    MeasurableSet.iInter fun m => (h m.property).measurableSet_nullSet
  have hBc : ∀ n, μ n (B n)ᶜ = 0 := by
    intro n
    simp only [B, compl_iInter]
    exact measure_iUnion_null fun m => (h m.property).measure_compl_nullSet
  have hBz : ∀ n m, n ≠ m → μ n (B m) = 0 := by
    intro n m hnm
    exact measure_mono_null (iInter_subset _ (⟨n, hnm⟩ : {n : ℕ // n ≠ m}))
      (h hnm).measure_nullSet
  refine ⟨disjointed B, MeasurableSet.disjointed hBm, disjoint_disjointed B, ?_, ?_⟩
  · intro n
    rw [disjointed_eq_inter_compl, compl_inter]
    apply measure_union_null (hBc n)
    rw [compl_iInter]
    apply measure_iUnion_null
    intro m
    rw [compl_iInter]
    apply measure_iUnion_null
    intro hmn
    simpa only [compl_compl] using hBz n m (Nat.ne_of_gt hmn)
  · intro n m hnm
    exact measure_mono_null (disjointed_subset B m) (hBz n m hnm)

end ThesisCommon
