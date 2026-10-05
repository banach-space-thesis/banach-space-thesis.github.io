import ThesisCommon.Analysis.ALPrincipalBandDecomposition
import ThesisCommon.Analysis.OperatorAlgebraLpSelfCopies

/-! Actual countable self-similarity of a principal band from disjoint
generators whose bands are isometric to it. The fibre isometries remain an
explicit input here, independently of any homogeneous matching theorem. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  (e : E) (a : ℕ → E)
  (hband : ∀ n, principalBand (a n) ≤ principalBand e)
  (hd : Pairwise (fun n m => |a n| ⊓ |a m| = 0))
  (hsum : HasSum a e)
  (d : ∀ n, principalBand (a n) ≃ₗᵢ[ℝ] principalBand e)

def alPrincipalBandSequenceEquiv :
    principalBand e ≃ₗᵢ[ℝ] lp (fun _ : ℕ => principalBand e) 1 :=
  (alPrincipalBandDecomposition hAL e a hband hd hsum).trans
    (lebesgueLpCoordinateEquiv (by simp : 0 < (1 : ENNReal).toReal) d)

theorem alPrincipalBandSequenceEquiv_apply (x : principalBand e) (n : ℕ) :
    alPrincipalBandSequenceEquiv hAL e a hband hd hsum d x n =
      d n (alPrincipalBandCoordinates hAL e a hd x n) := rfl

theorem alPrincipalBandSequenceEquiv_nonneg_iff
    (hdpos : ∀ n x, 0 ≤ d n x ↔ 0 ≤ x) (x : principalBand e) :
    (∀ n, 0 ≤ alPrincipalBandSequenceEquiv hAL e a hband hd hsum d x n) ↔ 0 ≤ x := by
  simp only [alPrincipalBandSequenceEquiv_apply, hdpos]
  exact alPrincipalBandDecomposition_nonneg_iff hAL e a hband hd hsum x

include hAL a hband hd hsum d in
theorem exists_orthogonal_selfCopies_principalBand_of_partition :
    ∃ J P : ℕ → principalBand e →L[ℝ] principalBand e,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id ℝ _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) :=
  exists_orthogonal_selfCopies_of_sequence_equiv
    (alPrincipalBandSequenceEquiv hAL e a hband hd hsum d).toContinuousLinearEquiv

end ThesisCommon
