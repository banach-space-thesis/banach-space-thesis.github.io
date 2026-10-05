import Posets.ProductIdealTransport
import Posets.ProductQuotientCoordinates
import Posets.ScalarMatrixProduct

/-! Diagonal evaluation kernels give distinct genuine closed ideals in the
concrete incidence operator algebra on c₀(P), for arbitrary posets P. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P]

theorem incidence_scalarMatrix_diagonal_mul (S T : incidenceSubalgebra 𝕜 P) (p : P) :
    scalarMatrix 𝕜 (S.val * T.val) p p =
      scalarMatrix 𝕜 S.val p p * scalarMatrix 𝕜 T.val p p := by
  letI : Nonempty P := ⟨p⟩
  rw [scalarMatrix_mul]
  apply tsum_eq_single p
  intro q hqp
  by_cases hpq : p ≤ q
  · have hnot : ¬ q ≤ p := fun h => hqp (le_antisymm h hpq)
    rw [T.property q p hnot, mul_zero]
  · rw [S.property p q hpq, zero_mul]

def incidenceCoordinateEvaluation (p : P) : CZeroOn 𝕜 P →L[𝕜] 𝕜 where
  toFun f := f ⟨p⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_czero_evaluation (𝕜 := 𝕜) (⟨p⟩ : Discrete P)

def incidenceCoordinatePoint (p : P) : incidenceSubalgebra 𝕜 P :=
  ⟨(incidenceCoordinateEvaluation (𝕜 := 𝕜) p).smulRight (unitVector 𝕜 p), by
    intro s t hst
    change ((if p = t then 1 else 0) : 𝕜) * (if s = p then 1 else 0) = 0
    by_cases hsp : s = p
    · subst s
      have hpt : p ≠ t := fun h => hst (h ▸ le_rfl)
      simp [hpt]
    · simp [hsp]⟩

@[simp] theorem incidenceCoordinatePoint_diagonal (p q : P) :
    scalarMatrix 𝕜 (incidenceCoordinatePoint (𝕜 := 𝕜) p).val q q =
      if q = p then 1 else 0 := by
  change ((if p = q then 1 else 0) : 𝕜) * (if q = p then 1 else 0) =
    if q = p then 1 else 0
  by_cases h : q = p
  · subst q; simp
  · simp [h]

def incidenceDiagonalKernel (p : P) : ClosedIdeal 𝕜 (incidenceSubalgebra 𝕜 P) := by
  refine ⟨{T | scalarMatrix 𝕜 T.val p p = 0}, ?_, rfl, ?_, ?_, ?_⟩
  · exact isClosed_singleton.preimage
      ((continuous_scalarMatrix p p).comp continuous_subtype_val)
  · intro S hS T hT
    change scalarMatrix 𝕜 S.val p p + scalarMatrix 𝕜 T.val p p = 0
    rw [hS, hT, add_zero]
  · intro c T hT
    change c • scalarMatrix 𝕜 T.val p p = 0
    rw [hT, smul_zero]
  · intro S T hT
    change scalarMatrix 𝕜 (S.val * T.val) p p = 0 ∧
      scalarMatrix 𝕜 (T.val * S.val) p p = 0
    rw [incidence_scalarMatrix_diagonal_mul, incidence_scalarMatrix_diagonal_mul, hT,
      mul_zero, zero_mul]
    exact ⟨rfl, rfl⟩

def incidenceDiagonalKernelEmbedding : P ↪ ClosedIdeal 𝕜 (incidenceSubalgebra 𝕜 P) where
  toFun := incidenceDiagonalKernel
  inj' := by
    intro p q hpq
    change incidenceDiagonalKernel (𝕜 := 𝕜) p = incidenceDiagonalKernel (𝕜 := 𝕜) q at hpq
    by_contra hne
    have hq : incidenceCoordinatePoint (𝕜 := 𝕜) p ∈ (incidenceDiagonalKernel (𝕜 := 𝕜) q).val := by
      change scalarMatrix 𝕜 _ q q = 0
      simp [Ne.symm hne]
    rw [← hpq] at hq
    change scalarMatrix 𝕜 _ p p = 0 at hq
    simp at hq

theorem finite_poset_of_finite_incidence_closedIdeals
    [Finite (ClosedIdeal 𝕜 (incidenceSubalgebra 𝕜 P))] : Finite P :=
  Finite.of_injective (incidenceDiagonalKernelEmbedding (𝕜 := 𝕜) (P := P))
    (incidenceDiagonalKernelEmbedding (𝕜 := 𝕜) (P := P)).injective

theorem infinite_incidence_closedIdeals [Infinite P] :
    Infinite (ClosedIdeal 𝕜 (incidenceSubalgebra 𝕜 P)) :=
  Infinite.of_injective (incidenceDiagonalKernelEmbedding (𝕜 := 𝕜) (P := P))
    (incidenceDiagonalKernelEmbedding (𝕜 := 𝕜) (P := P)).injective

theorem finite_poset_of_represented_incidence_finite_ideals
    {C : Type} [NormedRing C] [NormedAlgebra 𝕜 C]
    (h : RepresentedBy 𝕜 C (CZeroOn 𝕜 P) (incidenceOperators 𝕜 P))
    [Finite (ClosedIdeal 𝕜 C)] : Finite P := by
  obtain ⟨e, he⟩ := representedBy_subalgebra_coordinates (incidenceSubalgebra 𝕜 P) h
  letI : Finite (ClosedIdeal 𝕜 (incidenceSubalgebra 𝕜 P)) :=
    Finite.of_equiv (ClosedIdeal 𝕜 C)
      (closedIdealLinearEquivOrderIso e.toContinuousLinearEquiv he).toEquiv
  exact finite_poset_of_finite_incidence_closedIdeals (𝕜 := 𝕜)

end Posets
