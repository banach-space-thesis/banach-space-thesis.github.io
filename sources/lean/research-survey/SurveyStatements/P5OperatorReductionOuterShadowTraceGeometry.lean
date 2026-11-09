import SurveyStatements.P5L1VariationOriginalLocalTrace

/-! Genuine descendant packets for a fixed finite dyadic parent, with
the exact cardinal and trace-average identities. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5L1Variation
variable {𝕜 : Type*} [RCLike 𝕜]

def shadowDescendants (r : ℕ) (S : Finset (Fin (2 ^ r))) (j : ℕ) :
    Finset (Fin (2 ^ (r + j))) :=
  S.biUnion (terminalFiber (r + j) r (by omega))

theorem shadowDescendants_pairwise (r : ℕ) (S : Finset (Fin (2 ^ r))) (j : ℕ) :
    (S : Set (Fin (2 ^ r))).PairwiseDisjoint
      (terminalFiber (r + j) r (by omega)) := by
  intro a _ b _ hab
  exact terminalFiber_disjoint_roots (r + j) r (by omega) a b hab

theorem shadowDescendants_card (r : ℕ) (S : Finset (Fin (2 ^ r))) (j : ℕ) :
    (shadowDescendants r S j).card =
      ∑ root ∈ S, (terminalFiber (r + j) r (by omega) root).card :=
  Finset.card_biUnion (shadowDescendants_pairwise r S j)

theorem shadowDescendants_sum (r : ℕ) (S : Finset (Fin (2 ^ r))) (j : ℕ)
    (a : Fin (2 ^ (r + j)) → 𝕜) :
    (∑ k ∈ shadowDescendants r S j, a k) =
      ∑ root ∈ S, ∑ k ∈ terminalFiber (r + j) r (by omega) root, a k :=
  Finset.sum_biUnion (shadowDescendants_pairwise r S j)

theorem shadowDescendants_parent (r : ℕ) (S : Finset (Fin (2 ^ r))) (j : ℕ) :
    lpHaarBlockParent (r + j) (shadowDescendants r S j) = lpHaarBlockParent r S := by
  ext x
  simp only [lpHaarBlockParent, mem_iUnion]
  constructor
  · rintro ⟨k, hk, hx⟩
    obtain ⟨root, hr, hk⟩ := Finset.mem_biUnion.mp hk
    have hroot : x ∈ ⋃ a ∈ terminalFiber (r + j) r (by omega) root,
        lpHaarCell (r + j) a := mem_iUnion₂.mpr ⟨k, hk, hx⟩
    rw [terminalFiber_cells] at hroot
    exact ⟨root, hr, hroot⟩
  · rintro ⟨root, hr, hx⟩
    rw [← terminalFiber_cells (r + j) r (by omega) root] at hx
    obtain ⟨k, hk, hx⟩ := mem_iUnion₂.mp hx
    exact ⟨k, Finset.mem_biUnion.mpr ⟨root, hr, hk⟩, hx⟩

theorem equalDyadicLevelAverage_eq_shadowDescendants
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (r : ℕ) (S : Finset (Fin (2 ^ r))) (j : ℕ) :
    equalDyadicLevelAverage 𝕜 R r S j =
      ((shadowDescendants r S j).card : 𝕜)⁻¹ *
        ∑ k ∈ shadowDescendants r S j,
          haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) (r + j) k := by
  have hc : ((shadowDescendants r S j).card : 𝕜) =
      ∑ root ∈ S, ((terminalFiber (r + j) r (by omega) root).card : 𝕜) := by
    rw [shadowDescendants_card]
    simp only [Nat.cast_sum]
  rw [equalDyadicLevelAverage_eq_descendant_average, hc, shadowDescendants_sum]

end SurveyStatements.P5OperatorReduction
