import ThesisCommon.Analysis.ProjectionDecomposition
import ThesisCommon.Analysis.SequenceSumEquivs

/-! Pełczyński's decomposition method in the form used by the two papers.
If X is its own countable ℓp (or c₀) sum and X,Y embed complementably into
one another, their concrete product decompositions give X ≃L Y.
The proof expands the countable repetition and absorption argument explicitly.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y A B V W : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Absorb one A coordinate into a repeated A component of X. -/
def absorbProductEquiv (e : X ≃L[𝕜] X × (V × W)) (h : V ≃L[𝕜] A × V) :
    (X × A) ≃L[𝕜] X :=
  (e.prodCongr (ContinuousLinearEquiv.refl 𝕜 A)).trans
    ((ContinuousLinearEquiv.prodAssoc 𝕜 X (V × W) A).trans
      (((ContinuousLinearEquiv.refl 𝕜 X).prodCongr
        ((ContinuousLinearEquiv.prodComm 𝕜 (V × W) A).trans
          ((ContinuousLinearEquiv.prodAssoc 𝕜 A V W).symm.trans
            (h.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 W))))).trans e.symm))

/-- The decomposition method for every actual ℓp sum, including infinity. -/
def lpDecompositionEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (eX : X ≃L[𝕜] lp (fun _ : ℕ => X) p)
    (eXY : X ≃L[𝕜] Y × B) (eYX : Y ≃L[𝕜] X × A) : X ≃L[𝕜] Y := by
  let e := eXY.trans (eYX.prodCongr (ContinuousLinearEquiv.refl 𝕜 B))
  let eSum := (lpMapEquiv (ι := ℕ) p e).trans
    ((lpProdEquiv p).trans
      (((lpProdEquiv p).prodCongr
        (ContinuousLinearEquiv.refl 𝕜 (lp (fun _ : ℕ => B) p))).trans
          (ContinuousLinearEquiv.prodAssoc 𝕜 _ _ _)))
  let eStable := (eX.trans eSum).trans
    (eX.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 _))
  exact (eYX.trans (absorbProductEquiv eStable (lpHeadTailEquiv p))).symm

/-- The same countable repetition and absorption argument for actual c₀. -/
def cZeroDecompositionEquiv (eX : X ≃L[𝕜] CZeroSum X)
    (eXY : X ≃L[𝕜] Y × B) (eYX : Y ≃L[𝕜] X × A) : X ≃L[𝕜] Y := by
  let e := eXY.trans (eYX.prodCongr (ContinuousLinearEquiv.refl 𝕜 B))
  let eSum := (cZeroMapEquiv (ι := ℕ) e).trans
    (cZeroProdEquiv.trans
      ((cZeroProdEquiv.prodCongr
        (ContinuousLinearEquiv.refl 𝕜 (CZeroSum B))).trans
          (ContinuousLinearEquiv.prodAssoc 𝕜 _ _ _)))
  let eStable := (eX.trans eSum).trans
    (eX.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 _))
  exact (eYX.trans (absorbProductEquiv eStable cZeroHeadTailEquiv)).symm

/-- PFP gives primariness when the required sequence self-similarity is proved.
No such implication is asserted for an arbitrary normed space. -/
theorem HasPFP.isPrimary_of_sequenceSelfSimilar
    (h : HasPFP 𝕜 X) (hX : IsSequenceSelfSimilar 𝕜 X) : IsPrimary 𝕜 X := by
  have step (P : X →L[𝕜] X) (hP : P.comp P = P) (hf : FactorsIdentity P X) :
      Nonempty (X ≃L[𝕜] LinearMap.range P.toLinearMap) := by
    obtain ⟨U, ⟨eYX⟩⟩ := hf.projection_range_decomposition
    let eXY := projectionRangeKerEquiv P hP
    rcases hX with hLp | hZero
    · obtain ⟨p, ⟨eX⟩⟩ := hLp
      exact ⟨lpDecompositionEquiv p.val eX eXY eYX⟩
    · obtain ⟨eX⟩ := hZero
      exact ⟨cZeroDecompositionEquiv eX eXY eYX⟩
  intro P hP
  rcases h P with hp | hq
  · exact Or.inl (step P hP hp)
  · exact Or.inr (step _ (complementary_projection hP) hq)

theorem HasUPFP.isPrimary_of_sequenceSelfSimilar
    (h : HasUPFP 𝕜 X) (hX : IsSequenceSelfSimilar 𝕜 X) : IsPrimary 𝕜 X :=
  h.hasPFP.isPrimary_of_sequenceSelfSimilar hX

end ThesisCommon
