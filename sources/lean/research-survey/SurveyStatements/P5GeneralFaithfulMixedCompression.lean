import SurveyStatements.P5FaithfulMixedBlocks
import SurveyStatements.P5VectorTreeNatural

/-! Exact coordinates of faithful compression for arbitrary bounded mixed
operators. No diagonal or level-separation hypothesis occurs in these identities. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {Fo Fi : BiTree.SignedTree} {hp : p ≠ ∞}

def faithfulMixedBlockReader (Fo Fi : BiTree.SignedTree) (I J : DyadicIndex) :
    MixedNorm 𝕜 p →L[𝕜] 𝕜 :=
  ((Fo.block I).reader 𝕜 ⟨p, Fact.out⟩).comp
    (((Fi.block J).reader 𝕜 ⟨1, le_rfl⟩).compLpL p unitIntervalMeasure)

theorem faithfulMixed_inner_reading_coordinate
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (J : DyadicIndex) (f : MixedNorm 𝕜 p) :
    (dyadicHaarCoordinate 𝕜 1 J).compLpL p unitIntervalMeasure
      (D.inner.A.compLpL p unitIntervalMeasure f) =
      ((Fi.block J).reader 𝕜 ⟨1, le_rfl⟩).compLpL p unitIntervalMeasure f := by
  have hread (g : Lp 𝕜 1 unitIntervalMeasure) :
      dyadicHaarCoordinate 𝕜 1 J (D.inner.A g) =
        (Fi.block J).reader 𝕜 ⟨1, le_rfl⟩ g := by
    rw [dyadicHaarCoordinate_eq_support]
    have h := Fi.toPartitionTree.reading_coefficient 𝕜 ⟨1, le_rfl⟩ (by simp)
      D.inner.A D.inner.scalar_backward_limit J.1 J.2 g
    rw [Fi.nodeReader_eq 𝕜 ⟨1, le_rfl⟩ J.1 J.2] at h
    exact h
  apply Lp.ext
  filter_upwards [(dyadicHaarCoordinate 𝕜 1 J).coeFn_compLpL
      (D.inner.A.compLpL p unitIntervalMeasure f), D.inner.A.coeFn_compLpL f,
    ((Fi.block J).reader 𝕜 ⟨1, le_rfl⟩).coeFn_compLpL f]
    with x hx hi hr
  rw [hx, hi, hr]
  exact hread (f x)

theorem faithfulMixed_rawA_coordinate
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp)
    (I J : DyadicIndex) (f : MixedNorm 𝕜 p) :
    productHaarCoordinate 𝕜 p I J (D.rawA f) =
      faithfulMixedBlockReader (𝕜 := 𝕜) (p := p) Fo Fi I J f := by
  have hnatural := VectorPartitionTree.backward_limit_natural (𝕜 := 𝕜) (p := p)
    Fo.toPartitionTree hp D.outer.A Os.A D.outer.backward_limit Os.backward_limit
    ((Fi.block J).reader 𝕜 ⟨1, le_rfl⟩) f
  change dyadicHaarCoordinate 𝕜 p I
    ((dyadicHaarCoordinate 𝕜 1 J).compLpL p unitIntervalMeasure
      (D.inner.A.compLpL p unitIntervalMeasure (D.outer.A f))) = _
  rw [faithfulMixed_inner_reading_coordinate D J]
  calc
    _ = dyadicHaarCoordinate 𝕜 p I (Os.A
        (((Fi.block J).reader 𝕜 ⟨1, le_rfl⟩).compLpL p unitIntervalMeasure f)) :=
      congrArg (dyadicHaarCoordinate 𝕜 p I) hnatural.symm
    _ = _ := by
      rw [dyadicHaarCoordinate_eq_support]
      have h := Fo.toPartitionTree.reading_coefficient 𝕜 ⟨p, Fact.out⟩ hp
        Os.A Os.scalar_backward_limit I.1 I.2
        (((Fi.block J).reader 𝕜 ⟨1, le_rfl⟩).compLpL p unitIntervalMeasure f)
      rw [Fo.nodeReader_eq 𝕜 ⟨p, Fact.out⟩ I.1 I.2] at h
      exact h

theorem faithfulMixed_arbitrary_compression_coordinate
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (I J K L : DyadicIndex) :
    productHaarCoordinate 𝕜 p I J (D.rawA (T (D.rawB (productHaar 𝕜 p K L)))) =
      faithfulMixedBlockReader (𝕜 := 𝕜) (p := p) Fo Fi I J
        (T (tensorWith ((Fi.block L).vector 𝕜 ⟨1, le_rfl⟩)
          ((Fo.block K).vector 𝕜 ⟨p, Fact.out⟩))) := by
  rw [faithfulMixed_rawA_coordinate D Os, faithfulMixed_rawB_productHaar D Os]

theorem arbitraryOperator_signed_blocks
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (S R : LpHaarFiniteSplit) :
    T (tensorWith (R.vector 𝕜 ⟨1, le_rfl⟩) (S.vector 𝕜 ⟨p, Fact.out⟩)) =
      ∑ l ∈ R.atoms, ∑ k ∈ S.atoms,
        signedValue (R.signs l) (signedValue (S.signs k)
          (T (productHaar 𝕜 p ⟨S.level, k⟩ ⟨R.level, l⟩))) := by
  rw [LpHaarFiniteSplit.vector, lpHaarSignedBlock, tensorWith_sum_inner, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [LpHaarFiniteSplit.vector, lpHaarSignedBlock, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [tensorWith_signed_outer (𝕜 := 𝕜) (p := p),
    tensorWith_signed_inner (𝕜 := 𝕜) (p := p)]
  cases S.signs k <;> cases R.signs l <;>
    simp only [signedValue, if_true, Bool.false_eq_true, if_false,
      map_neg, productHaar, dyadicHaar_eq_support]

theorem faithfulMixed_arbitrary_compression_coordinate_sum
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (I J K L : DyadicIndex) :
    productHaarCoordinate 𝕜 p I J (D.rawA (T (D.rawB (productHaar 𝕜 p K L)))) =
      ∑ l ∈ (Fi.block L).atoms, ∑ k ∈ (Fo.block K).atoms,
        signedValue ((Fi.block L).signs l) (signedValue ((Fo.block K).signs k)
          (faithfulMixedBlockReader (𝕜 := 𝕜) (p := p) Fo Fi I J
            (T (productHaar 𝕜 p ⟨(Fo.block K).level, k⟩ ⟨(Fi.block L).level, l⟩)))) := by
  rw [faithfulMixed_arbitrary_compression_coordinate D Os,
    arbitraryOperator_signed_blocks T, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases (Fo.block K).signs k <;> cases (Fi.block L).signs l <;>
    simp only [signedValue, if_true, Bool.false_eq_true, if_false, map_neg]

end SurveyStatements.P5
