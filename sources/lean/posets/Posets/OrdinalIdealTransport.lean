import Posets.IdealCorrespondenceGeneral
import Posets.ProductIdealClosed
import Mathlib.Topology.Algebra.Module.StrongTopology

/-! Maximal closed operator ideals are invariant under Banach-space isomorphisms. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

section Algebras
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Mul B]

def multiplicativeContinuousLinearEquivHom (e : A ≃L[𝕜] B)
    (hm : ∀ a b, e (a*b) = e a * e b) : BoundedHom 𝕜 A B where
  toContinuousLinearMap := e.toContinuousLinearMap
  map_mul' := hm

theorem multiplicativeContinuousLinearEquiv_symm (e : A ≃L[𝕜] B)
    (hm : ∀ a b, e (a*b) = e a * e b) (a b : B) :
    e.symm (a*b) = e.symm a * e.symm b := by
  apply e.injective
  simp only [e.apply_symm_apply, hm]

def continuousAlgebraIdealOrderIso (e : A ≃L[𝕜] B)
    (hm : ∀ a b, e (a*b) = e a * e b) : ClosedIdeal 𝕜 A ≃o ClosedIdeal 𝕜 B where
  toFun I := ⟨e.symm ⁻¹' I.val, closedIdeal_preimage
    (multiplicativeContinuousLinearEquivHom e.symm
      (multiplicativeContinuousLinearEquiv_symm e hm)) I.property⟩
  invFun J := ⟨e ⁻¹' J.val,
    closedIdeal_preimage (multiplicativeContinuousLinearEquivHom e hm) J.property⟩
  left_inv I := by apply Subtype.ext; ext x; simp
  right_inv J := by apply Subtype.ext; ext x; simp
  map_rel_iff' := by
    intro I J
    change (e.symm ⁻¹' I.val ⊆ e.symm ⁻¹' J.val) ↔ I.val ⊆ J.val
    constructor
    · intro h x hx
      have h' := h (a := e x) (by simpa using hx)
      simpa using h'
    · exact Set.preimage_mono

theorem uniqueMaximalClosed_iff_uniqueCoatom :
    HasUniqueMaximalClosedIdeal 𝕜 A ↔ ∃! I : ClosedIdeal 𝕜 A, IsCoatom I := by
  constructor
  · rintro ⟨I, hI, hu⟩
    refine ⟨⟨I, hI.1⟩, (closedIdeal_maximal_iff_isCoatom _).mp hI, ?_⟩
    intro J hJ
    exact Subtype.ext (hu J.val ((closedIdeal_maximal_iff_isCoatom _).mpr hJ))
  · rintro ⟨I, hI, hu⟩
    refine ⟨I.val, (closedIdeal_maximal_iff_isCoatom I).mpr hI, ?_⟩
    intro J hJ
    exact congrArg Subtype.val (hu ⟨J, hJ.1⟩ ((closedIdeal_maximal_iff_isCoatom _).mp hJ))

theorem uniqueMaximalClosed_of_closedIdealOrderIso (e : ClosedIdeal 𝕜 A ≃o ClosedIdeal 𝕜 B) :
    HasUniqueMaximalClosedIdeal 𝕜 A ↔ HasUniqueMaximalClosedIdeal 𝕜 B := by
  rw [uniqueMaximalClosed_iff_uniqueCoatom, uniqueMaximalClosed_iff_uniqueCoatom]
  exact e.toEquiv.existsUnique_congr (fun I => (e.isCoatom_iff I).symm)

theorem uniqueMaximalClosed_continuousAlgebraEquiv (e : A ≃L[𝕜] B)
    (hm : ∀ a b, e (a*b) = e a * e b) :
    HasUniqueMaximalClosedIdeal 𝕜 A ↔ HasUniqueMaximalClosedIdeal 𝕜 B :=
  uniqueMaximalClosed_of_closedIdealOrderIso (continuousAlgebraIdealOrderIso e hm)

end Algebras

section Operators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def operatorConjugationEquiv (e : E ≃L[𝕜] F) :
    (E →L[𝕜] E) ≃L[𝕜] (F →L[𝕜] F) := e.arrowCongr e

@[simp] theorem operatorConjugationEquiv_apply (e : E ≃L[𝕜] F)
    (T : E →L[𝕜] E) (y : F) : operatorConjugationEquiv e T y = e (T (e.symm y)) := rfl

theorem operatorConjugationEquiv_mul (e : E ≃L[𝕜] F) (T S : E →L[𝕜] E) :
    operatorConjugationEquiv e (T*S) = operatorConjugationEquiv e T * operatorConjugationEquiv e S := by
  ext y
  simp only [ContinuousLinearMap.mul_apply, operatorConjugationEquiv_apply, e.symm_apply_apply]

/-- This transport uses the actual bounded conjugation of endomorphisms. -/
theorem uniqueMaximalClosed_operator_equiv (e : E ≃L[𝕜] F) :
    HasUniqueMaximalClosedIdeal 𝕜 (E →L[𝕜] E) ↔
      HasUniqueMaximalClosedIdeal 𝕜 (F →L[𝕜] F) :=
  uniqueMaximalClosed_continuousAlgebraEquiv (operatorConjugationEquiv e)
    (operatorConjugationEquiv_mul e)

end Operators
end Posets
