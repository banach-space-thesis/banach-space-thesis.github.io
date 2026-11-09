import BanachIsometric.Functional
import BanachIsometric.Statements
import Mathlib.Analysis.InnerProductSpace.Completion

/-! Compatible Hermitian norms retain the given norm and complex action.
Their completions are Hilbert spaces, and actual finite-dimensional subspaces
of equal complex dimension are complex-linearly isometric. -/

noncomputable section
namespace BanachIsometric
open UniformSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def ComplexIsHilbertForNorm : Prop :=
  CompleteSpace V ∧ HasHermitianSquare (norm : V → ℝ)

theorem complex_completion_hasHermitianSquare
    (hV : HasHermitianSquare (norm : V → ℝ)) :
    HasHermitianSquare (norm : Completion V → ℝ) := by
  obtain ⟨h, hdiag⟩ := hV
  letI : InnerProductSpace ℂ V := h.toInnerProductSpace hdiag
  exact norm_hasHermitianSquare

theorem complex_completion_isHilbertForNorm
    (hV : HasHermitianSquare (norm : V → ℝ)) :
    ComplexIsHilbertForNorm (V := Completion V) :=
  ⟨inferInstance, complex_completion_hasHermitianSquare hV⟩

theorem complex_linearIsometryEquiv_of_hermitian_finrank_eq
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hV : HasHermitianSquare (norm : V → ℝ))
    (hW : HasHermitianSquare (norm : W → ℝ))
    (hdim : Module.finrank ℂ V = Module.finrank ℂ W) :
    Nonempty (V ≃ₗᵢ[ℂ] W) := by
  obtain ⟨h, hdiag⟩ := hV
  obtain ⟨k, kdiag⟩ := hW
  letI : InnerProductSpace ℂ V := h.toInnerProductSpace hdiag
  letI : InnerProductSpace ℂ W := k.toInnerProductSpace kdiag
  exact ⟨(stdOrthonormalBasis ℂ V).equiv (stdOrthonormalBasis ℂ W) (finCongr hdim)⟩

theorem complex_metricSubspaceHomogeneity_of_hasHermitianSquare
    (hV : HasHermitianSquare (norm : V → ℝ)) (n : ℕ) :
    MetricSubspaceHomogeneity ℂ V n := by
  obtain ⟨h, hdiag⟩ := hV
  letI : InnerProductSpace ℂ V := h.toInnerProductSpace hdiag
  intro Y Z hY hZ
  letI : FiniteDimensional ℂ Y := Module.finite_of_rank_eq_nat hY
  letI : FiniteDimensional ℂ Z := Module.finite_of_rank_eq_nat hZ
  have hdim : Module.finrank ℂ Y = Module.finrank ℂ Z :=
    (Module.finrank_eq_of_rank_eq hY).trans (Module.finrank_eq_of_rank_eq hZ).symm
  exact ⟨((stdOrthonormalBasis ℂ Y).equiv (stdOrthonormalBasis ℂ Z) (finCongr hdim)).toIsometryEquiv⟩

end BanachIsometric
