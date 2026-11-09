import BanachIsometric.SignedCountAdditivity
import BanachIsometric.SignedCountExcision

/-! # Actual signed-count additivity over finite compact source decompositions -/

namespace BanachIsometric

open MeasureTheory Set
open scoped NNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem ae_signedFiberCount_finset_union
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0} (hf : LipschitzWith C f)
    {ι : Type*} (J : Finset ι) (s : ι → Set E)
    (hcompact : ∀ i ∈ J, IsCompact (s i))
    (hnull : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → μ (s i ∩ s j) = 0) :
    ∀ᵐ y ∂μ, signedFiberCount f (fderiv ℝ f) (⋃ i ∈ J, s i) y =
      ∑ i ∈ J, signedFiberCount f (fderiv ℝ f) (s i) y := by
  classical
  revert hcompact hnull
  induction J using Finset.induction_on with
  | empty =>
      intro _ _
      have hz (y : E) : signedFiberCount f (fderiv ℝ f) ∅ y = 0 :=
        signedFiberCount_eq_zero_of_not_mem_image f (fderiv ℝ f) ∅ y (by simp)
      simpa using ae_of_all μ hz
  | @insert i J hi ih =>
      intro hcompact hnull
      have hcompactJ : ∀ j ∈ J, IsCompact (s j) := fun j hj =>
        hcompact j (Finset.mem_insert_of_mem hj)
      have hnullJ : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → μ (s j ∩ s k) = 0 :=
        fun j hj k hk hjk => hnull j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) hjk
      have hinter : μ (s i ∩ ⋃ j ∈ J, s j) = 0 := by
        simp only [Set.inter_iUnion]
        apply (measure_biUnion_null_iff J.finite_toSet.countable).mpr
        intro j hj
        apply hnull i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        intro hij
        exact hi (hij ▸ hj)
      have hbin := ae_signedFiberCount_union_of_compact μ hf
        (hcompact i (Finset.mem_insert_self _ _)) (J.isCompact_biUnion hcompactJ) hinter
      filter_upwards [hbin, ih hcompactJ hnullJ] with y hybin hyJ
      simpa only [Finset.set_biUnion_insert, Finset.sum_insert hi, hyJ] using hybin

theorem ae_signedFiberCount_fintype_union_of_disjoint
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0} (hf : LipschitzWith C f)
    {ι : Type*} [Fintype ι] (s : ι → Set E) (hcompact : ∀ i, IsCompact (s i))
    (hdisjoint : Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∀ᵐ y ∂μ, signedFiberCount f (fderiv ℝ f) (⋃ i, s i) y =
      ∑ i, signedFiberCount f (fderiv ℝ f) (s i) y := by
  classical
  have h := ae_signedFiberCount_finset_union μ hf Finset.univ s (fun i _ => hcompact i)
    (fun i _ j _ hij => by rw [Set.disjoint_iff_inter_eq_empty.mp (hdisjoint hij), measure_empty])
  simpa using h

end BanachIsometric
