import SurveyStatements.P5GeneralMixedErrorIndexing
import SurveyStatements.P5GeneralMixedErrorTraceStrips

/-! Canonical strip and mixed indices recover exactly the three
off-diagonal classes of an arbitrary product-Haar matrix. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem generalMixed_outer_strip_matrix_sum
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (A B I R : DyadicIndex) :
    (∑' q : GeneralMixedStripIndex, if q.val.2 = R then
      a I q.val.1 I q.val.2 * (if (A, B) = (I, q.val.1) then 1 else 0) else 0) =
      if A = I ∧ B ≠ R then a I B I R else 0 := by
  have hpoint : (fun q : GeneralMixedStripIndex => if q.val.2 = R then
      a I q.val.1 I q.val.2 * (if (A, B) = (I, q.val.1) then 1 else 0) else 0) =
      (fun q : GeneralMixedStripIndex => if q.val = (B, R) then
        (if A = I then a I B I R else 0) else 0) := by
    funext q
    rcases q with ⟨⟨J, L⟩, hJL⟩
    change (if L = R then a I J I L * (if (A, B) = (I, J) then 1 else 0) else 0) =
      (if (J, L) = (B, R) then (if A = I then a I B I R else 0) else 0)
    by_cases hq : (J, L) = (B, R)
    · rcases Prod.mk.inj hq with ⟨rfl, rfl⟩
      by_cases hA : A = I <;> simp [hA]
    · by_cases hLR : L = R
      · have hBJ : B ≠ J := fun h => hq (Prod.ext h.symm hLR)
        have hJB : J ≠ B := Ne.symm hBJ
        simp [hLR, hBJ, hJB, Prod.mk.injEq, hq]
      · simp [hLR, hq]
  rw [hpoint]
  calc
    _ = (∑' q : {q : DyadicIndex × DyadicIndex // q.1 ≠ q.2},
        @ite 𝕜 (q.val = (B, R)) (Classical.propDecidable _)
          (if A = I then a I B I R else 0) 0) := by
      apply tsum_congr
      intro q
      by_cases hq : q.val = (B, R) <;> simp [hq]
    _ = @ite 𝕜 (B ≠ R) (Classical.propDecidable _)
        (if A = I then a I B I R else 0) 0 :=
      generalMixed_subtype_single_sum (fun q : DyadicIndex × DyadicIndex => q.1 ≠ q.2)
        (B, R) (if A = I then a I B I R else 0)
    _ = _ := by
      by_cases hA : A = I <;> by_cases hBR : B = R <;> simp [hA, hBR]

theorem generalMixed_inner_strip_matrix_sum
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (A B L J : DyadicIndex) :
    (∑' q : GeneralMixedStripIndex, if q.val.2 = L then
      a q.val.1 J q.val.2 J * (if (A, B) = (q.val.1, J) then 1 else 0) else 0) =
      if A ≠ L ∧ B = J then a A J L J else 0 := by
  have hpoint : (fun q : GeneralMixedStripIndex => if q.val.2 = L then
      a q.val.1 J q.val.2 J * (if (A, B) = (q.val.1, J) then 1 else 0) else 0) =
      (fun q : GeneralMixedStripIndex => if q.val = (A, L) then
        (if B = J then a A J L J else 0) else 0) := by
    funext q
    rcases q with ⟨⟨I, K⟩, hIK⟩
    change (if K = L then a I J K J * (if (A, B) = (I, J) then 1 else 0) else 0) =
      (if (I, K) = (A, L) then (if B = J then a A J L J else 0) else 0)
    by_cases hq : (I, K) = (A, L)
    · rcases Prod.mk.inj hq with ⟨rfl, rfl⟩
      by_cases hB : B = J <;> simp [hB]
    · by_cases hKL : K = L
      · have hAI : A ≠ I := fun h => hq (Prod.ext h.symm hKL)
        have hIA : I ≠ A := Ne.symm hAI
        simp [hKL, hAI, hIA, Prod.mk.injEq, hq]
      · simp [hKL, hq]
  rw [hpoint]
  calc
    _ = (∑' q : {q : DyadicIndex × DyadicIndex // q.1 ≠ q.2},
        @ite 𝕜 (q.val = (A, L)) (Classical.propDecidable _)
          (if B = J then a A J L J else 0) 0) := by
      apply tsum_congr
      intro q
      by_cases hq : q.val = (A, L) <;> simp [hq]
    _ = @ite 𝕜 (A ≠ L) (Classical.propDecidable _)
        (if B = J then a A J L J else 0) 0 :=
      generalMixed_subtype_single_sum (fun q : DyadicIndex × DyadicIndex => q.1 ≠ q.2)
        (A, L) (if B = J then a A J L J else 0)
    _ = _ := by
      by_cases hB : B = J <;> by_cases hAL : A = L <;> simp [hB, hAL]

theorem generalMixed_nuclear_matrix_sum
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (I J K L : DyadicIndex) :
    (∑' q : GeneralMixedNuclearIndex,
      if q.val.2 = (K, L) ∧ q.val.1 = (I, J) then
        a q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2 else 0) =
      if I ≠ K ∧ J ≠ L then a I J K L else 0 := by
  have hpoint : (fun q : GeneralMixedNuclearIndex =>
      if q.val.2 = (K, L) ∧ q.val.1 = (I, J) then
        a q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2 else 0) =
      (fun q : GeneralMixedNuclearIndex =>
        if q.val = ((I, J), (K, L)) then a I J K L else 0) := by
    funext q
    rcases q with ⟨⟨⟨A, B⟩, ⟨C, D⟩⟩, hq⟩
    by_cases hA : A = I <;> by_cases hB : B = J
      <;> by_cases hC : C = K <;> by_cases hD : D = L
      <;> simp [hA, hB, hC, hD, Prod.mk.injEq]
  rw [hpoint]
  calc
    _ = (∑' q : {q : (DyadicIndex × DyadicIndex) × (DyadicIndex × DyadicIndex) //
          q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2},
        @ite 𝕜 (q.val = ((I, J), (K, L))) (Classical.propDecidable _)
          (a I J K L) 0) := by
      apply tsum_congr
      intro q
      by_cases hq : q.val = ((I, J), (K, L)) <;> simp [hq]
    _ = @ite 𝕜 (I ≠ K ∧ J ≠ L) (Classical.propDecidable _) (a I J K L) 0 :=
      generalMixed_subtype_single_sum
        (fun q : (DyadicIndex × DyadicIndex) × (DyadicIndex × DyadicIndex) =>
          q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2) ((I, J), (K, L)) (a I J K L)
    _ = _ := by
      by_cases h : I ≠ K ∧ J ≠ L <;> simp [h]

theorem mixedNuclearError_canonical_coordinate (hp : p ≠ ∞)
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (b : GeneralMixedNuclearIndex → ℝ) (hb : Summable b)
    (hbudget : ∀ q : GeneralMixedNuclearIndex,
      ‖a q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2‖ *
        (‖cancellativeHaarCoordinate 𝕜 p q.val.2.1 q.val.2.2‖ *
          ‖cancellativeHaar 𝕜 p q.val.1.1 q.val.1.2‖) ≤ b q)
    (I J K L : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p I J
      (mixedNuclearError (𝕜 := 𝕜) (p := p)
        (fun q : GeneralMixedNuclearIndex => q.val.2)
        (fun q : GeneralMixedNuclearIndex => q.val.1)
        (fun q => a q.val.1.1 q.val.1.2 q.val.2.1 q.val.2.2)
        (cancellativeHaar 𝕜 p K L)) =
      if I ≠ K ∧ J ≠ L then a I J K L else 0 :=
  (mixedNuclearError_coordinate hp _ _ _ b hb hbudget I J K L).trans
    (generalMixed_nuclear_matrix_sum a I J K L)

end SurveyStatements.P5
