import SurveyStatements.P5BiTreeStabilizationBounds
import SurveyStatements.P5BiTreeStabilizationBudget

/-! Actual two-parameter coefficient stabilization of every bounded
array, on two genuine signed faithful trees with separated frequencies.
The two limiting scalars are fixed before the error budgets are chosen. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem roundSymbol_semiStable (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (H : IteratedTraceData d M) (η : ℕ → ℕ → ℝ)
    (hη : ∀ i j, 0 < η i j) {δ : ℝ} (hδ : 0 < δ)
    (ε : ℕ → ℝ) (hεδ : ∀ n, ε n ≤ δ / 100)
    (hεη : ∀ n i j, i ≤ n + 1 → j ≤ n + 1 → ε n ≤ η i j / 100)
    (r : (n : ℕ) → LevelPairs n)
    (hr : ∀ n, RoundSpec d H ε n (fun i : Fin n => r i.val) (r n)) :
    SemiStable (roundSymbol d r) η δ := by
  constructor
  · intro I J b hJI
    have h := lower_edge_bound d H ε r hr I J hJI b
    have h0 := hεη I.1 I.1 J.1 (by omega) (by omega)
    have h1 := hεη (I.1 + 1) I.1 J.1 (by omega) (by omega)
    linarith [hη I.1 J.1]
  · intro I J b hIJ
    have h := upper_edge_bound d H ε r hr I J hIJ b
    have h0 := hεη J.1 I.1 J.1 (by omega) (by omega)
    have h1 := hεη (J.1 + 1) I.1 J.1 (by omega) (by omega)
    linarith [hη I.1 J.1]
  · intro I J b c hIJ
    have h := diagonal_edge_bound d H ε r hr I J hIJ b c
    have h0 := hεη I.1 I.1 I.1 (by omega) (by omega)
    have h1 := hεη (I.1 + 1) I.1 I.1 (by omega) (by omega)
    linarith [hη I.1 I.1]
  · intro I J b e hJ
    obtain ⟨K, hK, c, rfl⟩ := exists_dyadic_parent J I.1 hJ
    have h := superdiagonal_edge_bound d H ε r hr I K hK.symm c b e
    have h0 := hεη I.1 I.1 (I.1 + 1) (by omega) (by omega)
    have h1 := hεη (I.1 + 1) I.1 (I.1 + 1) (by omega) (by omega)
    have h2 := hεη (I.1 + 2) I.1 (I.1 + 1) (by omega) (by omega)
    linarith [hη I.1 (I.1 + 1)]
  · have h1 := root_upper_bound d H ε r hr true
    have h2 : ‖rectangleMean H.upperTrace LpHaarFiniteParent.root LpHaarFiniteParent.root -
        roundSymbol d r root (child root false)‖ < ε 1 + ε 0 + ε 0 := by
      simpa only [norm_sub_rev] using root_upper_bound d H ε r hr false
    have h := norm_sub_lt_pair h1 h2
    linarith [hεδ 0, hεδ 1]

theorem exists_stabilized_trees (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (hM : 0 ≤ M) (hd : ∀ I J, ‖d I J‖ ≤ M) :
    ∃ lam mu : 𝕜, ∀ η : ℕ → ℕ → ℝ, (∀ i j, 0 < η i j) →
      ∀ δ : ℝ, 0 < δ →
      ∃ Fo Fi : SignedTree,
        (∀ i j, i < j → (Fo.node i).level < (Fo.node j).level) ∧
        (∀ i j, i < j → (Fi.node i).level < (Fi.node j).level) ∧
        SemiStable (compressedSymbol d Fo Fi) η δ ∧
        ‖compressedSymbol d Fo Fi root root - lam‖ < δ ∧
        ‖compressedSymbol d Fo Fi root (child root true) - mu‖ < δ := by
  let H := Classical.choice (exists_iterated_trace_data d hM hd)
  let lam := rectangleMean H.lowerTrace LpHaarFiniteParent.root LpHaarFiniteParent.root
  let mu := rectangleMean H.upperTrace LpHaarFiniteParent.root LpHaarFiniteParent.root
  refine ⟨lam, mu, fun η hη δ hδ => ?_⟩
  obtain ⟨ε, hε, hεδ, hεη⟩ := exists_round_error_budget η hη hδ
  obtain ⟨r, hr⟩ := exists_ordered_round_sequence d hM H ε hε
  let hr' (n : ℕ) := (hr n).toRoundSpec
  let Fo := (roundOuterTree d H ε r hr').toSequentialSplits
  let Fi := (roundInnerTree d H ε r hr').toSequentialSplits
  have hsymbol (I J : DyadicIndex) : compressedSymbol d Fo Fi I J = roundSymbol d r I J := by
    simp only [compressedSymbol, Fo, Fi, DyadicSignedTree.toSequentialSplits_block,
      roundOuterTree, roundInnerTree, roundSymbol]
  refine ⟨Fo, Fi, roundOuterTree_strict_frequencies d H ε r hr,
    roundInnerTree_strict_frequencies d H ε r hr, ?_, ?_, ?_⟩
  · have h := roundSymbol_semiStable d H η hη hδ ε hεδ hεη r hr'
    have heq : compressedSymbol d Fo Fi = roundSymbol d r := funext (fun I => funext (hsymbol I))
    rw [heq]
    exact h
  · rw [hsymbol]
    have h := root_lower_bound d H ε r hr'
    change ‖roundSymbol d r root root - lam‖ < ε 0 + ε 0 at h
    linarith [hεδ 0]
  · rw [hsymbol]
    have h := root_upper_bound d H ε r hr' true
    change ‖roundSymbol d r root (child root true) - mu‖ < ε 1 + ε 0 + ε 0 at h
    linarith [hεδ 0, hεδ 1]

end SurveyStatements.P5.BiTree
