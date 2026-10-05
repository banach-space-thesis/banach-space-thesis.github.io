import JLMS.OrdinalSpaceSplit
import JLMS.FinitePowerAutomaticContinuity
import JLMS.OperatorConjugation
import JLMS.JohnsonSquare

/-!
# The finite-power and square steps in the ordinal-space reduction

The actual interval splitting identifies C[0,α(n+1)] with the (n+1)-fold
power of C[0,α], for every infinite α. Thus automatic continuity passes
from the initial-ordinal case to its finite multiples by the matrix argument.
The square criterion is similarly connected directly to Johnson's theorem.
The classification theorem, which decides which case applies, is separate.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The finite-multiple decomposition in Section 9, with no classification assumption. -/
def ordinalSpaceFinitePower (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) (n : ℕ) :
    OrdinalC 𝕜 (α * ((n + 1 : ℕ) : Ordinal)) ≃L[𝕜] (Fin (n + 1) → OrdinalC 𝕜 α) := by
  induction n with
  | zero =>
    have heq : α * ((0 + 1 : ℕ) : Ordinal) = α := by simp
    rw [heq]
    exact (ContinuousLinearEquiv.piUnique 𝕜 (fun _ : Fin 1 => OrdinalC 𝕜 α)).symm
  | succ n e =>
    have hmul : α * ((n.succ + 1 : ℕ) : Ordinal) = α * ((n + 1 : ℕ) : Ordinal) + α := by
      rw [show n.succ + 1 = (n + 1).succ by rfl, Ordinal.natCast_succ, Ordinal.mul_succ]
    rw [hmul]
    exact (ordinalSpaceAddIsometry (𝕜 := 𝕜) (α * ((n + 1 : ℕ) : Ordinal)) α hα).toContinuousLinearEquiv.trans
      ((e.prodCongr (ContinuousLinearEquiv.refl 𝕜 _)).trans
        ((ContinuousLinearEquiv.prodComm 𝕜 _ _).trans
          (Fin.consEquivL 𝕜 (fun _ : Fin (n.succ + 1) => OrdinalC 𝕜 α))))

theorem continuous_ordinal_hom_of_finiteMultiple
    (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) (n : ℕ)
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    (hbase : ∀ ψ : (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →ₙₐ[𝕜] A, Continuous ψ)
    (φ : (OrdinalC 𝕜 (α * ((n + 1 : ℕ) : Ordinal)) →L[𝕜]
      OrdinalC 𝕜 (α * ((n + 1 : ℕ) : Ordinal))) →ₙₐ[𝕜] A) : Continuous φ := by
  apply continuous_operator_hom_of_conjugation (ordinalSpaceFinitePower α hα n) φ
  exact continuous_operator_hom_of_finitePower hbase _

/-- The exact square-isomorphism criterion used before the classification step. -/
theorem continuous_ordinal_hom_of_doubleIsomorphic
    (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α)
    (e : OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (α * 2))
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    (φ : (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →ₙₐ[𝕜] A) : Continuous φ := by
  exact johnson_automaticContinuity_of_square
    (e.trans (ordinalSpaceDoubleIsometry α hα).toContinuousLinearEquiv) φ

end JLMS
