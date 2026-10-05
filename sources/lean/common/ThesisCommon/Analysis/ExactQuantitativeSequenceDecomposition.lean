import ThesisCommon.Analysis.QuantitativeSquareDecomposition
import ThesisCommon.Analysis.ExactCZeroSumIsometries

/-! The sequence alternative of Appendix A, with exactly a⁴ b⁴ C⁴.
Both actual ℓp sequence spaces (including infinity) and actual c₀ are covered.
All intermediary identifications are norm-exact for the matching product. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y Z A B F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

def banachDirectSumIsometryCongr (r : BanachExponent)
    (e : X ≃ₗᵢ[𝕜] Y) (f : A ≃ₗᵢ[𝕜] B) :
    BanachDirectSum r X A ≃ₗᵢ[𝕜] BanachDirectSum r Y B :=
  isometryEquivOfNormBoundOne
    (banachDirectSumCongr r e.toContinuousLinearEquiv f.toContinuousLinearEquiv)
    ((equivNormBound_isometry e).banachDirectSumCongr r
      (equivNormBound_isometry f) zero_le_one)

theorem square_withBound_of_selfSimilar (r : BanachExponent) {C : ℝ}
    (hC : 1 ≤ C) (h : IsomorphicWithBound 𝕜 X Z C)
    (e : Z ≃ₗᵢ[𝕜] BanachDirectSum r X Z) :
    IsomorphicWithBound 𝕜 X (BanachDirectSum r X X) (C ^ 2) := by
  have h' := (h.trans (isomorphicWithBound_of_isometry e)).trans
    (h.symm.banachDirectSumLeft (Z := X) r hC)
  convert h' using 1
  ring

theorem exact_lp_decomposition_withBound (p : BanachExponent) {a b C : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hC : 1 ≤ C)
    (hXY : IsomorphicWithBound 𝕜 X (BanachDirectSum p Y F) a)
    (hYX : IsomorphicWithBound 𝕜 Y (BanachDirectSum p X H) b)
    (hX : IsomorphicWithBound 𝕜 X (SequenceSum p X) C) :
    IsomorphicWithBound 𝕜 X Y (a ^ 4 * b ^ 4 * C ^ 4) := by
  let W := BanachDirectSum p (SequenceSum p F) H
  let S := BanachDirectSum p (SequenceSum p Y) W
  have habC : 1 ≤ a * b * C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le ha hb) hC
  have hYS : IsomorphicWithBound 𝕜 Y S (a * b * C) := by
    have h₁ := hYX.trans (hX.banachDirectSumRight (Z := H) p hC)
    have h₂ := h₁.trans ((hXY.sequenceSum ha p).banachDirectSumRight (Z := H) p ha)
    have h₃ := h₂.trans ((isomorphicWithBound_of_isometry
      (sequenceProdIsometry (𝕜 := 𝕜) (X := Y) (Y := F) p)).banachDirectSumRight (Z := H) p le_rfl)
    have h₄ := h₃.trans (isomorphicWithBound_of_isometry
      (banachDirectSumAssoc (𝕜 := 𝕜) (X := SequenceSum p Y) (Y := SequenceSum p F) (Z := H) p))
    convert h₄ using 1
    ring
  let eS : S ≃ₗᵢ[𝕜] BanachDirectSum p Y S :=
    (banachDirectSumIsometryCongr p (sequenceHeadTailIsometry p)
      (LinearIsometryEquiv.refl 𝕜 W)).trans (banachDirectSumAssoc p)
  have hYY := square_withBound_of_selfSimilar p habC hYS eS
  have hXX := square_withBound_of_selfSimilar p hC hX (sequenceHeadTailIsometry p)
  have h := square_decomposition_withBound p ha hb (one_le_pow₀ hC) (one_le_pow₀ habC)
    hXY hYX hXX hYY
  convert h using 1
  ring

theorem exact_cZero_decomposition_withBound {a b C : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hC : 1 ≤ C)
    (hXY : IsomorphicWithBound 𝕜 X (BanachDirectSum ⟨∞, le_top⟩ Y F) a)
    (hYX : IsomorphicWithBound 𝕜 Y (BanachDirectSum ⟨∞, le_top⟩ X H) b)
    (hX : IsomorphicWithBound 𝕜 X (CZeroSum X) C) :
    IsomorphicWithBound 𝕜 X Y (a ^ 4 * b ^ 4 * C ^ 4) := by
  let r : BanachExponent := ⟨∞, le_top⟩
  let W := BanachDirectSum r (CZeroSum F) H
  let S := BanachDirectSum r (CZeroSum Y) W
  have habC : 1 ≤ a * b * C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le ha hb) hC
  have hYS : IsomorphicWithBound 𝕜 Y S (a * b * C) := by
    have h₁ := hYX.trans (hX.banachDirectSumRight (Z := H) r hC)
    have h₂ := h₁.trans ((hXY.cZeroSum ha).banachDirectSumRight (Z := H) r ha)
    have h₃ := h₂.trans ((isomorphicWithBound_of_isometry
      (cZeroBanachProdIsometry (𝕜 := 𝕜) (X := Y) (Y := F))).banachDirectSumRight (Z := H) r le_rfl)
    have h₄ := h₃.trans (isomorphicWithBound_of_isometry
      (banachDirectSumAssoc (𝕜 := 𝕜) (X := CZeroSum Y) (Y := CZeroSum F) (Z := H) r))
    convert h₄ using 1
    ring
  let eS : S ≃ₗᵢ[𝕜] BanachDirectSum r Y S :=
    (banachDirectSumIsometryCongr r cZeroBanachHeadTailIsometry
      (LinearIsometryEquiv.refl 𝕜 W)).trans (banachDirectSumAssoc r)
  have hYY := square_withBound_of_selfSimilar r habC hYS eS
  have hXX := square_withBound_of_selfSimilar r hC hX cZeroBanachHeadTailIsometry
  have h := square_decomposition_withBound r ha hb (one_le_pow₀ hC) (one_le_pow₀ habC)
    hXY hYX hXX hYY
  convert h using 1
  ring

theorem one_le_decompositionSequenceBound {C1 C2 C3 C4 C5 : ℝ}
    (h1 : 0 ≤ C1) (h3 : 0 ≤ C3) (h5 : 1 ≤ C5) :
    1 ≤ decompositionSequenceBound C1 C2 C3 C4 C5 := by
  unfold decompositionSequenceBound
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (one_le_decompositionAuxBound h1))
    (one_le_pow₀ (one_le_decompositionAuxBound h3))) (one_le_pow₀ h5)

theorem quantitativeDecomposition_sequence {C1 C2 C3 C4 C5 : ℝ}
    (h1 : 0 ≤ C1) (h2 : 1 ≤ C2) (h3 : 0 ≤ C3) (h4 : 1 ≤ C4) (h5 : 1 ≤ C5)
    (hXY : HasComplementedCopyWithBound 𝕜 X Y C1 C2)
    (hYX : HasComplementedCopyWithBound 𝕜 Y X C3 C4)
    (hStable : IsomorphicWithBound 𝕜 X (CZeroSum X) C5 ∨
      ∃ p : BanachExponent, IsomorphicWithBound 𝕜 X (SequenceSum p X) C5) :
    IsomorphicWithBound 𝕜 X Y (decompositionSequenceBound C1 C2 C3 C4 C5) := by
  rcases hStable with hZero | ⟨p, hLp⟩
  · obtain ⟨E, P, hP⟩ := hXY.exists_lp_decomposition ⟨∞, le_top⟩ h1 h2
    obtain ⟨G, Q, hQ⟩ := hYX.exists_lp_decomposition ⟨∞, le_top⟩ h3 h4
    exact exact_cZero_decomposition_withBound (one_le_decompositionAuxBound h1)
      (one_le_decompositionAuxBound h3) h5 hP hQ hZero
  · obtain ⟨E, P, hP⟩ := hXY.exists_lp_decomposition p h1 h2
    obtain ⟨G, Q, hQ⟩ := hYX.exists_lp_decomposition p h3 h4
    exact exact_lp_decomposition_withBound p (one_le_decompositionAuxBound h1)
      (one_le_decompositionAuxBound h3) h5 hP hQ hLp

end ThesisCommon
