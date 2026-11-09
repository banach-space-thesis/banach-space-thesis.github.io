import SurveyStatements.P5FaithfulMixedData
import SurveyStatements.P5FaithfulWeightedReading
import SurveyStatements.P5TensorBilinearity
import SurveyStatements.P5BiTreeStabilizationDefinitions
import SurveyStatements.P5HaarBiorthogonal

/-! Exact images of product-Haar vectors and weighted blocks under the
constructed faithful mixed maps. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {Fo Fi : BiTree.SignedTree} {hp : p ≠ ∞}

theorem faithfulMixed_rawB_productHaar
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp) (I J : DyadicIndex) :
    D.rawB (productHaar 𝕜 p I J) =
      tensorWith ((Fi.block J).vector 𝕜 ⟨1, le_rfl⟩)
        ((Fo.block I).vector 𝕜 ⟨p, Fact.out⟩) := by
  have hi : D.inner.B (dyadicHaar 𝕜 1 J) = (Fi.block J).vector 𝕜 ⟨1, le_rfl⟩ := by
    rw [dyadicHaar_eq_support]
    exact (Fi.toPartitionTree.embedding_haar 𝕜 ⟨1, le_rfl⟩ (by simp)
      D.inner.B D.inner.scalar_forward_limit J.1 J.2).trans
        (Fi.nodeVector_eq 𝕜 ⟨1, le_rfl⟩ J.1 J.2)
  have ho : Os.B (dyadicHaar 𝕜 p I) = (Fo.block I).vector 𝕜 ⟨p, Fact.out⟩ := by
    rw [dyadicHaar_eq_support]
    exact (Fo.toPartitionTree.embedding_haar 𝕜 ⟨p, Fact.out⟩ hp
      Os.B Os.scalar_forward_limit I.1 I.2).trans
        (Fo.nodeVector_eq 𝕜 ⟨p, Fact.out⟩ I.1 I.2)
  change D.outer.B ((D.inner.B.compLpL p unitIntervalMeasure) (productHaar 𝕜 p I J)) = _
  rw [productHaar, mixedInnerMap_tensor, hi]
  change D.outer.B (vectorTensor (𝕜 := 𝕜) _ _) = vectorTensor (𝕜 := 𝕜) _ _
  rw [VectorPartitionTree.forward_limit_tensor Fo.toPartitionTree hp
    D.outer.B Os.B D.outer.forward_limit Os.scalar_forward_limit, ho]

theorem faithfulMixed_outer_read_weighted
    (D : FaithfulMixedData 𝕜 p Fo.toPartitionTree Fi.toPartitionTree hp)
    (Os : FaithfulTreeMaps 𝕜 𝕜 p Fo.toPartitionTree hp)
    (hlevels : ∀ i j, i < j → (Fo.node i).level < (Fo.node j).level)
    (I : DyadicIndex) (g : Lp 𝕜 1 unitIntervalMeasure)
    (c : Fin (2 ^ (Fo.block I).level) → 𝕜) :
    D.outer.A (tensorWith g (lpHaarWeightedSplitVector 𝕜 ⟨p, Fact.out⟩ (Fo.block I) c)) =
      (((Fo.block I).atoms.card : 𝕜)⁻¹ * ∑ k ∈ (Fo.block I).atoms, c k) •
        tensorWith g (dyadicHaar 𝕜 p I) := by
  change D.outer.A (vectorTensor (𝕜 := 𝕜) g _) = _
  rw [VectorPartitionTree.backward_limit_tensor Fo.toPartitionTree hp
    D.outer.A Os.A D.outer.backward_limit Os.scalar_backward_limit]
  have hread : Os.A (lpHaarWeightedSplitVector 𝕜 ⟨p, Fact.out⟩ (Fo.block I) c) =
      (((Fo.block I).atoms.card : 𝕜)⁻¹ * ∑ k ∈ (Fo.block I).atoms, c k) •
        lpHaarDyadic 𝕜 ⟨p, Fact.out⟩ I.1 I.2 :=
    Fo.reading_weighted_block 𝕜 ⟨p, Fact.out⟩ hp hlevels Os.A
      Os.scalar_backward_limit I.1 I.2 c
  rw [hread, map_smul]
  rw [dyadicHaar_eq_support]
  rfl

theorem productMultiplier_signed_blocks
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜)
    (hT : ∀ I J, T (productHaar 𝕜 p I J) = d I J • productHaar 𝕜 p I J)
    (S R : LpHaarFiniteSplit) :
    T (tensorWith (R.vector 𝕜 ⟨1, le_rfl⟩) (S.vector 𝕜 ⟨p, Fact.out⟩)) =
      ∑ l ∈ R.atoms, tensorWith (signedValue (R.signs l)
        (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ R.level l))
        (lpHaarWeightedSplitVector 𝕜 ⟨p, Fact.out⟩ S
          (fun k => d ⟨S.level, k⟩ ⟨R.level, l⟩)) := by
  have hhaar (n m : ℕ) (k : Fin (2 ^ n)) (l : Fin (2 ^ m)) :
      T (tensorWith (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ m l)
        (lpHaarDyadic 𝕜 ⟨p, Fact.out⟩ n k)) =
          d ⟨n, k⟩ ⟨m, l⟩ • tensorWith (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ m l)
            (lpHaarDyadic 𝕜 ⟨p, Fact.out⟩ n k) := by
    simpa only [productHaar, dyadicHaar_eq_support] using hT ⟨n, k⟩ ⟨m, l⟩
  rw [LpHaarFiniteSplit.vector, lpHaarSignedBlock, tensorWith_sum_inner, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [LpHaarFiniteSplit.vector, lpHaarSignedBlock, lpHaarWeightedSplitVector,
    map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [tensorWith_signed_outer (𝕜 := 𝕜) (p := p),
    tensorWith_signed_inner (𝕜 := 𝕜) (p := p)]
  cases S.signs k <;> cases R.signs l <;>
    simp only [signedValue, if_true, Bool.false_eq_true, if_false,
      tensorWith_neg_inner, map_neg, map_smul, neg_neg, smul_neg, hhaar]

end SurveyStatements.P5
