import BanachIsometric.QuaternionicHilbertInverseLimit

/-! A Hermitian square for a right quaternionic seminorm descends through
its actual normed quotient. Kernel vanishing is proved from the specified
seminorm and canonical polarization, without an assumed Cauchy-Schwarz lemma. -/

namespace BanachIsometric.Quaternionic

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]

theorem realDiagonalPolar_eq_zero_of_seminorm_zero (p : RightSeminorm X)
    (x y : X) (hx : p x = 0) : realDiagonalPolar (fun z => p z ^ 2) x y = 0 := by
  have hqx : seminormQuotientMap p x = 0 := norm_eq_zero.mp (by rw [seminormQuotientMap_norm, hx])
  have hadd : p (x + y) = p y := by
    rw [← seminormQuotientMap_norm, map_add, hqx, zero_add, seminormQuotientMap_norm]
  have hsub : p (x - y) = p y := by
    rw [← seminormQuotientMap_norm, map_sub, hqx, zero_sub, norm_neg, seminormQuotientMap_norm]
  simp only [realDiagonalPolar, hadd, hsub, sub_self, zero_div]

theorem HermitianForm.eq_zero_of_seminorm_zero (h : HermitianForm X) (p : RightSeminorm X)
    (hdiag : ∀ x, h.form x x = (p x ^ 2 : ℝ)) (x y : X) (hx : p x = 0) : h.form x y = 0 := by
  rw [h.form_eq_quaternionPolar hdiag x y]
  apply Quaternion.ext
  · exact realDiagonalPolar_eq_zero_of_seminorm_zero p x y hx
  · exact realDiagonalPolar_eq_zero_of_seminorm_zero p (rightMul x i) y (by rw [p.right_mul, hx, zero_mul])
  · exact realDiagonalPolar_eq_zero_of_seminorm_zero p (rightMul x j) y (by rw [p.right_mul, hx, zero_mul])
  · exact realDiagonalPolar_eq_zero_of_seminorm_zero p (rightMul x k) y (by rw [p.right_mul, hx, zero_mul])

theorem HermitianForm.eq_zero_of_seminorm_zero_right (h : HermitianForm X) (p : RightSeminorm X)
    (hdiag : ∀ x, h.form x x = (p x ^ 2 : ℝ)) (x y : X) (hy : p y = 0) : h.form x y = 0 := by
  rw [← h.star_symm y x, h.eq_zero_of_seminorm_zero p hdiag y x hy, star_zero]

theorem HermitianForm.congr_of_seminormQuotientMap_eq (h : HermitianForm X) (p : RightSeminorm X)
    (hdiag : ∀ x, h.form x x = (p x ^ 2 : ℝ)) (x₁ x₂ y₁ y₂ : X)
    (hx : seminormQuotientMap p x₁ = seminormQuotientMap p x₂)
    (hy : seminormQuotientMap p y₁ = seminormQuotientMap p y₂) : h.form x₁ y₁ = h.form x₂ y₂ := by
  have hpx : p (x₁ - x₂) = 0 := by rw [← seminormQuotientMap_norm, map_sub, hx, sub_self, norm_zero]
  have hpy : p (y₁ - y₂) = 0 := by rw [← seminormQuotientMap_norm, map_sub, hy, sub_self, norm_zero]
  have hleft : h.form x₁ y₁ = h.form x₂ y₁ := sub_eq_zero.mp (by
    rw [← h.sub_left]
    exact h.eq_zero_of_seminorm_zero p hdiag _ _ hpx)
  have hright : h.form x₂ y₁ = h.form x₂ y₂ := sub_eq_zero.mp (by
    rw [← h.sub_right]
    exact h.eq_zero_of_seminorm_zero_right p hdiag _ _ hpy)
  exact hleft.trans hright

def HermitianForm.seminormQuotient (h : HermitianForm X) (p : RightSeminorm X)
    (hdiag : ∀ x, h.form x x = (p x ^ 2 : ℝ)) : HermitianForm (SeminormQuotient p) where
  form := SeparationQuotient.lift₂ (fun x y : SeminormModel p => h.form (x : X) (y : X)) (by
    intro x₁ x₂ y₁ y₂ hx hy
    apply h.congr_of_seminormQuotientMap_eq p hdiag
    · exact (hx.map (SeparationQuotient.mkCLM Hᵐᵒᵖ (SeminormModel p)).continuous).eq
    · exact (hy.map (SeparationQuotient.mkCLM Hᵐᵒᵖ (SeminormModel p)).continuous).eq)
  add_right x y z := by
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    refine Quotient.inductionOn z ?_
    intro c
    exact h.add_right a b c
  mul_right x y a := Quotient.ind₂ (fun v w => h.mul_right v w a) x y
  star_symm x y := Quotient.ind₂ (fun a b => h.star_symm a b) x y

@[simp] theorem HermitianForm.seminormQuotient_apply (h : HermitianForm X) (p : RightSeminorm X)
    (hdiag : ∀ x, h.form x x = (p x ^ 2 : ℝ)) (x y : X) :
    (h.seminormQuotient p hdiag).form (seminormQuotientMap p x) (seminormQuotientMap p y) = h.form x y := rfl

theorem quotient_hasHermitianSquare_of_seminormIsHilbertian (p : RightSeminorm X)
    (hp : SeminormIsHilbertian p) : HasHermitianSquare (norm : SeminormQuotient p → ℝ) := by
  obtain ⟨h, hdiag⟩ := hp
  let hQ := h.seminormQuotient p hdiag
  have hQdiag : ∀ z : SeminormQuotient p, hQ.form z z = (‖z‖ ^ 2 : ℝ) := by
    intro z
    obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective p z
    rw [seminormQuotientMap_norm]
    exact hdiag x
  refine ⟨hQ, hQdiag, ?_⟩
  intro z hz
  rw [hQdiag, Quaternion.re_coe]
  exact sq_pos_iff.mpr (norm_ne_zero_iff.mpr hz)

theorem seminormIsHilbertian_iff_quotient_square (p : RightSeminorm X) :
    SeminormIsHilbertian p ↔ HasHermitianSquare (norm : SeminormQuotient p → ℝ) :=
  ⟨quotient_hasHermitianSquare_of_seminormIsHilbertian p, seminormIsHilbertian_of_quotient_square p⟩

end
end BanachIsometric.Quaternionic
