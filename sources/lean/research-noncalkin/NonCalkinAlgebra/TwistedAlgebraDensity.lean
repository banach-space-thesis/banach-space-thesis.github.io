import NonCalkinAlgebra.TwistedFiniteSpan
import NonCalkinAlgebra.SeparatedDensity
import NonCalkinAlgebra.MetricCardinality
import Mathlib.SetTheory.Cardinal.Finsupp

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
universe u

section General
variable {G : Type u} [AddCommGroup G]

theorem one_le_norm_shift_sub (c : Cocycle G) (g h : G) (hgh : g ≠ h) :
    1 ≤ ‖shift c g - shift c h‖ := by
  classical
  let δ : SquareSummable G := lp.single 2 0 (1 : ℂ)
  have hδ : ‖δ‖ = 1 := by
    dsimp only [δ]
    rw [lp.norm_single (by norm_num), norm_one]
  have hx : ((shift c g - shift c h) δ) g = 1 := by
    change shift c g δ g - shift c h δ g = 1
    dsimp only [δ]
    rw [shift_single_zero, shift_single_zero]
    simp only [lp.coeFn_single, Pi.single_eq_same, Pi.single_eq_of_ne hgh, sub_zero]
  have hcoord := lp.norm_apply_le_norm (by norm_num) ((shift c g - shift c h) δ) g
  rw [hx, norm_one] at hcoord
  have hop := (shift c g - shift c h).le_opNorm δ
  rw [hδ, mul_one] at hop
  exact hcoord.trans hop

theorem density_lower_bound (c : Cocycle G)
    (S : Set (closedSubalgebra c)) (hS : Dense S) : Cardinal.mk G ≤ Cardinal.mk S := by
  apply cardinal_le_dense_of_separated (shiftInAlgebra c) _ S hS
  intro g h hgh
  change 1 ≤ ‖shift c g - shift c h‖
  exact one_le_norm_shift_sub c g h hgh

end General

section Continuum
variable {G : Type} [AddCommGroup G]

theorem cardinal_finiteSpan_le_continuum (c : Cocycle G)
    (hG : Cardinal.mk G ≤ Cardinal.continuum) :
    Cardinal.mk (finiteSpan c) ≤ Cardinal.continuum := by
  have hcoeff : Cardinal.mk (G →₀ ℂ) ≤ Cardinal.continuum := by
    rw [Cardinal.mk_finsupp_of_infinite', Cardinal.mk_complex]
    exact max_le hG le_rfl
  have hrange : (finiteSpan c : Set (SquareSummable G →L[ℂ] SquareSummable G)) =
      Set.range (Finsupp.linearCombination ℂ (shift c)) := by
    change (Submodule.span ℂ (Set.range (shift c)) :
      Set (SquareSummable G →L[ℂ] SquareSummable G)) = _
    rw [← Finsupp.range_linearCombination]
    rfl
  change Cardinal.mk (finiteSpan c : Set (SquareSummable G →L[ℂ] SquareSummable G)) ≤ _
  rw [hrange]
  exact Cardinal.mk_range_le.trans hcoeff

theorem cardinal_closedSubalgebra_le_continuum (c : Cocycle G)
    (hG : Cardinal.mk G ≤ Cardinal.continuum) :
    Cardinal.mk (closedSubalgebra c) ≤ Cardinal.continuum := by
  have h := cardinal_closure_le_continuum
    (finiteSpan c : Set (SquareSummable G →L[ℂ] SquareSummable G))
    (cardinal_finiteSpan_le_continuum c hG)
  rw [← coe_closedSubalgebra_eq_closure c] at h
  exact h

/-- At a continuum-sized binary group, the concrete closed twisted algebra
has density exactly continuum, with no simplicity or AF assumption. -/
theorem density_continuum (c : Cocycle G) (hG : Cardinal.mk G = Cardinal.continuum) :
    HasDensityCharacter (closedSubalgebra c) Cardinal.continuum := by
  have hcard : Cardinal.mk (closedSubalgebra c) = Cardinal.continuum := by
    apply le_antisymm (cardinal_closedSubalgebra_le_continuum c hG.le)
    simpa only [Cardinal.mk_univ, hG] using density_lower_bound c Set.univ dense_univ
  refine ⟨⟨Set.univ, dense_univ, ?_⟩, ?_⟩
  · simpa only [Cardinal.mk_univ] using hcard
  · intro S hS
    rw [← hG]
    exact density_lower_bound c S hS

end Continuum
end NonCalkinAlgebra.TwistedRegular
