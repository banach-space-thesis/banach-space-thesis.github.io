import ThesisCommon.ALSpace

/-! Actual real and imaginary coordinates of an abstract complex
Banach-lattice model, derived from its real-form decomposition. -/
noncomputable section
namespace ThesisCommon
namespace BanachLatticeModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

def imagPart (B : BanachLatticeModel ℂ E) : E →L[ℝ] B.realForm :=
  B.realPart.comp ((-Complex.I) • ContinuousLinearMap.id ℝ E)

theorem imagPart_apply (B : BanachLatticeModel ℂ E) (z : E) :
    B.imagPart z = B.realPart ((-Complex.I) • z) := rfl

theorem imagPart_coe (B : BanachLatticeModel ℂ E) (x : B.realForm) :
    B.imagPart (x : E) = 0 := by
  rw [imagPart_apply, neg_smul, map_neg]
  simpa using congrArg Neg.neg (B.realPart_I x)

theorem imagPart_I (B : BanachLatticeModel ℂ E) (z : E) :
    B.imagPart (Complex.I • z) = B.realPart z := by
  simp only [imagPart_apply, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

theorem realPart_I_eq_neg_imagPart (B : BanachLatticeModel ℂ E) (z : E) :
    B.realPart (Complex.I • z) = -B.imagPart z := by
  simp only [imagPart_apply, neg_smul, map_neg, neg_neg]

theorem realPart_smul (B : BanachLatticeModel ℂ E) (c : ℂ) (z : E) :
    B.realPart (c • z) = c.re • B.realPart z - c.im • B.imagPart z := by
  have hcast (a : ℝ) (w : E) : (a : ℂ) • w = a • w := by
    simpa only [Complex.real_smul, mul_one, one_smul] using (smul_assoc a (1 : ℂ) w)
  conv_lhs => rw [← c.re_add_im]
  rw [add_smul, mul_smul, hcast, hcast, map_add, map_smul, map_smul,
    realPart_I_eq_neg_imagPart, smul_neg, sub_eq_add_neg]

theorem imagPart_smul (B : BanachLatticeModel ℂ E) (c : ℂ) (z : E) :
    B.imagPart (c • z) = c.re • B.imagPart z + c.im • B.realPart z := by
  have hcast (a : ℝ) (w : E) : (a : ℂ) • w = a • w := by
    simpa only [Complex.real_smul, mul_one, one_smul] using (smul_assoc a (1 : ℂ) w)
  conv_lhs => rw [← c.re_add_im]
  rw [add_smul, mul_smul, hcast, hcast, map_add, map_smul, map_smul, imagPart_I]

theorem ext_real_imag (B : BanachLatticeModel ℂ E) {z w : E}
    (hr : B.realPart z = B.realPart w) (hi : B.imagPart z = B.imagPart w) : z = w := by
  calc
    z = (B.realPart z : E) + Complex.I • (B.imagPart z : E) := B.decomposition z
    _ = (B.realPart w : E) + Complex.I • (B.imagPart w : E) := by rw [hr, hi]
    _ = w := (B.decomposition w).symm

end BanachLatticeModel
end ThesisCommon
