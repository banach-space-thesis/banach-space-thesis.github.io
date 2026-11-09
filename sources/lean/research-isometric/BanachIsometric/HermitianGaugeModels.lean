import BanachIsometric.GaugeNormModel
import BanachIsometric.ComplexNormSimilarityProportionality
import BanachIsometric.QuaternionicGlobalProportionality

/-! Explicit positive Hermitian squares yield the real positive bilinear
norm model without changing the metric on the original vector space.
The original complex or right quaternionic action is retained on the tag. -/

namespace BanachIsometric.MetricGeometry

noncomputable section

section Complex

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]

def complexPositiveGaugeData {q : X → ℝ} (h : PositiveHermitianForm X)
    (hdiag : ∀ x, h.form x x = (q x ^ 2 : ℝ)) (hnonneg : ∀ x, 0 ≤ q x) :
    PositiveGaugeData q where
  bilinear := LinearMap.mk₂ ℝ (fun x y => (h.form x y).re)
    (fun x y z => by
      change (h.form (x + y) z).re = (h.form x z).re + (h.form y z).re
      rw [h.map_add_left, Complex.add_re])
    (fun r x y => by
      change (h.form (r • x) y).re = r * (h.form x y).re
      rw [← algebraMap_smul ℂ r x, h.map_smul_left]
      simp)
    (fun x y z => by
      change (h.form x (y + z)).re = (h.form x y).re + (h.form x z).re
      rw [h.add_right, Complex.add_re])
    (fun r x y => by
      change (h.form x (r • y)).re = r * (h.form x y).re
      rw [← algebraMap_smul ℂ r y, h.smul_right]
      simp)
  symmetric x y := by simpa only [Complex.conj_re] using congrArg Complex.re (h.conj_symm x y)
  diagonal x := congrArg Complex.re (hdiag x)
  nonneg := hnonneg
  eq_zero_iff x := by
    constructor
    · intro hx
      by_contra hxn
      have hp := h.self_pos x hxn
      rw [hdiag, hx] at hp
      norm_num at hp
    · rintro rfl
      have hz := congrArg Complex.re (hdiag 0)
      have hh := h.add_right (0 : X) 0 0
      rw [add_zero] at hh
      have hzero : h.form 0 0 = 0 := (add_eq_left.mp hh.symm)
      rw [hzero, Complex.zero_re, Complex.ofReal_re] at hz
      exact sq_eq_zero_iff.mp hz.symm

end Complex

section Quaternionic

open Quaternionic

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [IsScalarTower ℝ Hᵐᵒᵖ X]

def quaternionicPositiveGaugeData {q : X → ℝ} (h : HermitianForm X)
    (hdiag : ∀ x, h.form x x = (q x ^ 2 : ℝ)) (hpos : h.IsPositiveDefinite)
    (hnonneg : ∀ x, 0 ≤ q x) : PositiveGaugeData q where
  bilinear := LinearMap.mk₂ ℝ (fun x y => (h.form x y).re)
    (fun x y z => by
      change (h.form (x + y) z).re = (h.form x z).re + (h.form y z).re
      rw [h.add_left, Quaternion.re_add])
    (fun r x y => by
      change (h.form (r • x) y).re = r * (h.form x y).re
      rw [← rightMul_real x r, h.mul_left]; simp)
    (fun x y z => by
      change (h.form x (y + z)).re = (h.form x y).re + (h.form x z).re
      rw [h.add_right, Quaternion.re_add])
    (fun r x y => by
      change (h.form x (r • y)).re = r * (h.form x y).re
      rw [← rightMul_real y r, h.mul_right]; simp [mul_comm])
  symmetric x y := by simpa only [Quaternion.re_star] using congrArg QuaternionAlgebra.re (h.star_symm x y)
  diagonal x := congrArg QuaternionAlgebra.re (hdiag x)
  nonneg := hnonneg
  eq_zero_iff x := by
    constructor
    · intro hx
      by_contra hxn
      have hp := hpos x hxn
      rw [hdiag, hx] at hp
      norm_num at hp
    · rintro rfl
      have hz := congrArg QuaternionAlgebra.re (hdiag 0)
      rw [h.zero_right, Quaternion.re_zero, Quaternion.re_coe] at hz
      exact sq_eq_zero_iff.mp hz.symm

end Quaternionic

end
end BanachIsometric.MetricGeometry


