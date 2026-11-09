import SurveyStatements.P5FaithfulMixedBlocks
import SurveyStatements.P5HaarMultipliers

/-! Exact double-block symbols of actual contractive multiplier compression. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem faithfulMixed_compression_productHaar {Fo Fi : BiTree.SignedTree} {hp : p ≠ ∞}
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp)
    (hlevels_o : ∀ i j, i < j → (Fo.node i).level < (Fo.node j).level)
    (hlevels_i : ∀ i j, i < j → (Fi.node i).level < (Fi.node j).level)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜)
    (hT : ∀ I J, T (productHaar 𝕜 p I J) = d I J • productHaar 𝕜 p I J)
    (I J : DyadicIndex) :
    D.rawA (T (D.rawB (productHaar 𝕜 p I J))) =
      BiTree.compressedSymbol d Fo Fi I J • productHaar 𝕜 p I J := by
  let S := Fo.block I
  let R := Fi.block J
  let c (l : Fin (2 ^ R.level)) : 𝕜 :=
    (S.atoms.card : 𝕜)⁻¹ * ∑ k ∈ S.atoms, d ⟨S.level, k⟩ ⟨R.level, l⟩
  have houter : D.outer.A (T (tensorWith (R.vector 𝕜 ⟨1, le_rfl⟩)
      (S.vector 𝕜 ⟨p, Fact.out⟩))) =
        tensorWith (lpHaarWeightedSplitVector 𝕜 ⟨1, le_rfl⟩ R c) (dyadicHaar 𝕜 p I) := by
    rw [productMultiplier_signed_blocks T d hT S R, map_sum,
      lpHaarWeightedSplitVector, tensorWith_sum_inner]
    apply Finset.sum_congr rfl
    intro l _
    rw [faithfulMixed_outer_read_weighted D Os hlevels_o]
    change c l • tensorWith (signedValue (R.signs l)
      (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ R.level l)) (dyadicHaar 𝕜 p I) =
        tensorWith (signedValue (R.signs l)
          (c l • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ R.level l)) (dyadicHaar 𝕜 p I)
    rw [tensorWith_signed_inner, tensorWith_signed_inner, tensorWith_smul_inner]
    cases R.signs l <;> simp [signedValue]
  have havg : (R.atoms.card : 𝕜)⁻¹ * ∑ l ∈ R.atoms, c l =
      BiTree.blockAverage d S R := by
    have hsum : (∑ l ∈ R.atoms, c l) =
        (S.atoms.card : 𝕜)⁻¹ * ∑ k ∈ S.atoms, ∑ l ∈ R.atoms,
          d ⟨S.level, k⟩ ⟨R.level, l⟩ := by
      dsimp only [c]
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    rw [hsum]
    dsimp only [BiTree.blockAverage]
    ring
  have hinner : D.inner.A (lpHaarWeightedSplitVector 𝕜 ⟨1, le_rfl⟩ R c) =
      ((R.atoms.card : 𝕜)⁻¹ * ∑ l ∈ R.atoms, c l) • dyadicHaar 𝕜 1 J := by
    simpa only [R, BiTree.SignedTree.block, dyadicHaar_eq_support] using
      Fi.reading_weighted_block 𝕜 ⟨1, le_rfl⟩ (by simp) hlevels_i D.inner.A
        D.inner.scalar_backward_limit J.1 J.2 c
  rw [faithfulMixed_rawB_productHaar D Os]
  change D.inner.A.compLpL p unitIntervalMeasure
    (D.outer.A (T (tensorWith (R.vector 𝕜 ⟨1, le_rfl⟩)
      (S.vector 𝕜 ⟨p, Fact.out⟩)))) = _
  rw [houter, mixedInnerMap_tensor, hinner,
    tensorWith_smul_inner (𝕜 := 𝕜) (p := p), havg]
  rw [productHaar, dyadicHaar_eq_support]
  rfl

theorem exists_faithful_multiplier_compression (hp : p ≠ ∞)
    (Fo Fi : BiTree.SignedTree)
    (hlevels_o : ∀ i j, i < j → (Fo.node i).level < (Fo.node j).level)
    (hlevels_i : ∀ i j, i < j → (Fi.node i).level < (Fi.node j).level)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (hT : IsProductHaarMultiplier T d) :
    ∃ A B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) ∧
      IsProductHaarMultiplier ((A.comp T).comp B) (BiTree.compressedSymbol d Fo Fi) := by
  obtain ⟨D⟩ := exists_faithfulMixedData (𝕜 := 𝕜) Fo.toPartitionTree
    Fi.toPartitionTree hp Fo.faithful Fi.faithful
  obtain ⟨Os⟩ := exists_faithfulTreeMaps (𝕜 := 𝕜) (E := 𝕜)
    Fo.toPartitionTree hp Fo.faithful
  let U : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
    (DoublyZeroMean 𝕜 p).subtypeL.comp (T.comp (cancellativeProjection 𝕜 p))
  have hfix (x : DoublyZeroMean 𝕜 p) : cancellativeProjection 𝕜 p x.val = x :=
    congrArg (fun L : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p => L x)
      (cancellativeProjection_retraction 𝕜 p)
  have hU : ∀ I J, U (productHaar 𝕜 p I J) = d I J • productHaar 𝕜 p I J := by
    intro I J
    change (T (cancellativeProjection 𝕜 p (cancellativeHaar 𝕜 p I J).val)).val = _
    rw [hfix, hT I J]
    rfl
  refine ⟨D.A Fo.faithful Fi.faithful, D.B, D.norm_A Fo.faithful Fi.faithful,
    D.norm_B, D.retraction Fo.faithful Fi.faithful, ?_⟩
  intro I J
  apply Subtype.ext
  have h := faithfulMixed_compression_productHaar D Os hlevels_o hlevels_i U d hU I J
  change D.rawA (U (D.B (cancellativeHaar 𝕜 p I J)).val) = _ at h
  change D.rawA (T (cancellativeProjection 𝕜 p
    (D.B (cancellativeHaar 𝕜 p I J)).val)).val = _ at h
  have ht := congrArg
    (fun z : DoublyZeroMean 𝕜 p => D.rawA (T z).val)
    (hfix (D.B (cancellativeHaar 𝕜 p I J)))
  exact ht.symm.trans h

end SurveyStatements.P5
