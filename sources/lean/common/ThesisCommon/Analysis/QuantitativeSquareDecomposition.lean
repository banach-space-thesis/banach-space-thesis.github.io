import ThesisCommon.Analysis.QuantitativeLpProducts

/-! The square alternative of the quantitative decomposition argument.
Every step uses the fixed genuine ℓr norm and actual bounded equivalences,
giving precisely the source bound a² b² C5 C6. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

theorem one_le_decompositionAuxBound {P C : ℝ} (hP : 0 ≤ P) :
    1 ≤ decompositionAuxBound P C := by
  have hs := Real.sqrt_nonneg C
  have hm := mul_nonneg hs hP
  unfold decompositionAuxBound
  nlinarith

theorem square_absorption_withBound (r : BanachExponent) {a C : ℝ}
    (ha : 1 ≤ a) (hC : 1 ≤ C)
    (hXY : IsomorphicWithBound 𝕜 X (BanachDirectSum r Y F) a)
    (hYY : IsomorphicWithBound 𝕜 Y (BanachDirectSum r Y Y) C) :
    IsomorphicWithBound 𝕜 X (BanachDirectSum r Y X) (a ^ 2 * C) := by
  have h₁ := hXY.trans (hYY.banachDirectSumRight (Z := F) r hC)
  have h₂ := h₁.trans (isomorphicWithBound_of_isometry
    (banachDirectSumAssoc (𝕜 := 𝕜) (X := Y) (Y := Y) (Z := F) r))
  have h₃ := h₂.trans (hXY.symm.banachDirectSumLeft (Z := Y) r ha)
  convert h₃ using 1
  ring

theorem square_decomposition_withBound (r : BanachExponent) {a b C D : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hXY : IsomorphicWithBound 𝕜 X (BanachDirectSum r Y F) a)
    (hYX : IsomorphicWithBound 𝕜 Y (BanachDirectSum r X H) b)
    (hXX : IsomorphicWithBound 𝕜 X (BanachDirectSum r X X) C)
    (hYY : IsomorphicWithBound 𝕜 Y (BanachDirectSum r Y Y) D) :
    IsomorphicWithBound 𝕜 X Y (a ^ 2 * b ^ 2 * C * D) := by
  have h₁ := square_absorption_withBound r ha hD hXY hYY
  have h₂ := square_absorption_withBound r hb hC hYX hXX
  have h := (h₁.trans (isomorphicWithBound_of_isometry
    (banachDirectSumComm (𝕜 := 𝕜) (X := Y) (Y := X) r))).trans h₂.symm
  convert h using 1
  ring

theorem one_le_decompositionSquareBound {C1 C2 C3 C4 C5 C6 : ℝ}
    (h1 : 0 ≤ C1) (h3 : 0 ≤ C3) (h5 : 1 ≤ C5) (h6 : 1 ≤ C6) :
    1 ≤ decompositionSquareBound C1 C2 C3 C4 C5 C6 := by
  unfold decompositionSquareBound
  have ha : 1 ≤ decompositionAuxBound C1 C2 ^ 2 :=
    one_le_pow₀ (one_le_decompositionAuxBound h1)
  have hb : 1 ≤ decompositionAuxBound C3 C4 ^ 2 :=
    one_le_pow₀ (one_le_decompositionAuxBound h3)
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) h5) h6

theorem quantitativeDecomposition_square {C1 C2 C3 C4 C5 C6 : ℝ}
    (h1 : 0 ≤ C1) (h2 : 1 ≤ C2) (h3 : 0 ≤ C3) (h4 : 1 ≤ C4)
    (h5 : 1 ≤ C5) (h6 : 1 ≤ C6)
    (hXY : HasComplementedCopyWithBound 𝕜 X Y C1 C2)
    (hYX : HasComplementedCopyWithBound 𝕜 Y X C3 C4)
    (hSq : ∃ r : BanachExponent,
      IsomorphicWithBound 𝕜 X (BanachDirectSum r X X) C5 ∧
      IsomorphicWithBound 𝕜 Y (BanachDirectSum r Y Y) C6) :
    IsomorphicWithBound 𝕜 X Y (decompositionSquareBound C1 C2 C3 C4 C5 C6) := by
  obtain ⟨r, hXX, hYY⟩ := hSq
  obtain ⟨E, P, hP⟩ := hXY.exists_lp_decomposition r h1 h2
  obtain ⟨G, Q, hQ⟩ := hYX.exists_lp_decomposition r h3 h4
  exact square_decomposition_withBound r (one_le_decompositionAuxBound h1)
    (one_le_decompositionAuxBound h3) h5 h6 hP hQ hXX hYY

end ThesisCommon
