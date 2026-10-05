import ThesisCommon.Analysis.ExactQuantitativeSequenceDecomposition

/-! Both classical decomposition alternatives, obtained from the quantitative
proofs with constants extracted from actual supplied isomorphisms. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem isomorphicWithBound_max_distortion (e : X ≃L[𝕜] Y) :
    IsomorphicWithBound 𝕜 X Y
      (max 1 (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖)) :=
  ⟨e, le_max_right _ _⟩

theorem HasComplementedCopy.exists_withBound (h : HasComplementedCopy 𝕜 X Y) :
    ∃ Cproj Ciso : ℝ, 0 ≤ Cproj ∧ 1 ≤ Ciso ∧
      HasComplementedCopyWithBound 𝕜 X Y Cproj Ciso := by
  obtain ⟨E, hE, P, hP, ⟨e⟩⟩ := h
  exact ⟨‖P‖, max 1 (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖),
    norm_nonneg P, le_max_left _ _, E, hE, P, hP, le_rfl, isomorphicWithBound_max_distortion e⟩

theorem pelczynskiDecomposition_full
    (hXY : HasComplementedCopy 𝕜 X Y) (hYX : HasComplementedCopy 𝕜 Y X)
    (hStable : (Nonempty (X ≃L[𝕜] X × X) ∧ Nonempty (Y ≃L[𝕜] Y × Y)) ∨
      IsSequenceSelfSimilar 𝕜 X) : Nonempty (X ≃L[𝕜] Y) := by
  obtain ⟨C1, C2, h1, h2, hXY⟩ := hXY.exists_withBound
  obtain ⟨C3, C4, h3, h4, hYX⟩ := hYX.exists_withBound
  rcases hStable with ⟨⟨eX⟩, ⟨eY⟩⟩ | hSeq
  · let r : BanachExponent := ⟨⊤, le_top⟩
    let fX : X ≃L[𝕜] BanachDirectSum r X X :=
      eX.trans (WithLp.prodContinuousLinearEquiv r.val 𝕜 X X).symm
    let fY : Y ≃L[𝕜] BanachDirectSum r Y Y :=
      eY.trans (WithLp.prodContinuousLinearEquiv r.val 𝕜 Y Y).symm
    obtain ⟨e, _⟩ := quantitativeDecomposition_square h1 h2 h3 h4
      (le_max_left 1 _) (le_max_left 1 _) hXY hYX
      ⟨r, isomorphicWithBound_max_distortion fX, isomorphicWithBound_max_distortion fY⟩
    exact ⟨e⟩
  · rcases hSeq with hLp | hZero
    · obtain ⟨p, ⟨eX⟩⟩ := hLp
      obtain ⟨e, _⟩ := quantitativeDecomposition_sequence h1 h2 h3 h4
        (le_max_left 1 _) hXY hYX (Or.inr ⟨p, isomorphicWithBound_max_distortion eX⟩)
      exact ⟨e⟩
    · obtain ⟨eX⟩ := hZero
      obtain ⟨e, _⟩ := quantitativeDecomposition_sequence h1 h2 h3 h4
        (le_max_left 1 _) hXY hYX (Or.inl (isomorphicWithBound_max_distortion eX))
      exact ⟨e⟩

end ThesisCommon
