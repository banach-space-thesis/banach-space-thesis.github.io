import BanachIsometric.SeminormTail
import BanachIsometric.ComplexPolarization

/-! A Hilbertian seminorm may have a radical. Its algebraic Hermitian form
therefore has no positive-definiteness field. We prove radical vanishing and
descend this actual form to the actual normed quotient, retaining the original
complex action. Conversely a quotient norm form pulls back to the seminorm. -/

noncomputable section
namespace BanachIsometric

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- An algebraic complex Hermitian form; positivity is specified by its
diagonal where needed, and degeneracy is allowed. -/
structure ComplexHermitianForm (X : Type*) [AddCommGroup X] [Module ℂ X] where
  form : X → X → ℂ
  conj_symm : ∀ x y, star (form x y) = form y x
  add_right : ∀ x y z, form x (y + z) = form x y + form x z
  smul_right : ∀ x y (a : ℂ), form x (a • y) = a * form x y

namespace ComplexHermitianForm

theorem add_left (h : ComplexHermitianForm X) (x y z : X) :
    h.form (x + y) z = h.form x z + h.form y z := by
  rw [← h.conj_symm z, h.add_right, star_add, h.conj_symm, h.conj_symm]

theorem smul_left (h : ComplexHermitianForm X) (a : ℂ) (x y : X) :
    h.form (a • x) y = star a * h.form x y := by
  rw [← h.conj_symm y, h.smul_right, star_mul, h.conj_symm, mul_comm]

theorem sub_left (h : ComplexHermitianForm X) (x y z : X) :
    h.form (x - y) z = h.form x z - h.form y z := by
  rw [sub_eq_add_neg, h.add_left, ← neg_one_smul ℂ y, h.smul_left]
  simp [sub_eq_add_neg]

theorem sub_right (h : ComplexHermitianForm X) (x y z : X) :
    h.form x (y - z) = h.form x y - h.form x z := by
  rw [sub_eq_add_neg, h.add_right, ← neg_one_smul ℂ z, h.smul_right]
  simp [sub_eq_add_neg]

theorem polarization (h : ComplexHermitianForm X) (x y : X) :
    h.form x y =
      (h.form (x + y) (x + y) - h.form (x - y) (x - y) +
        (h.form (x - Complex.I • y) (x - Complex.I • y) -
          h.form (x + Complex.I • y) (x + Complex.I • y)) * Complex.I) / 4 := by
  simp only [h.add_left, h.add_right, h.sub_left, h.sub_right,
    h.smul_left, h.smul_right, Complex.star_def, Complex.conj_I]
  linear_combination (h.form x y - h.form y x) / 2 * Complex.I_mul_I

theorem eq_complexPolar (h : ComplexHermitianForm X) {p : X → ℝ}
    (hdiag : ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ)) (x y : X) :
    h.form x y = complexPolar p x y := by
  rw [h.polarization]
  simp only [hdiag, complexPolar]

def comap {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (h : ComplexHermitianForm X) (f : Y →ₗ[ℂ] X) : ComplexHermitianForm Y where
  form x y := h.form (f x) (f y)
  conj_symm x y := h.conj_symm _ _
  add_right x y z := by rw [map_add, h.add_right]
  smul_right x y a := by rw [map_smul, h.smul_right]

end ComplexHermitianForm

def PositiveHermitianForm.toComplexHermitianForm (h : PositiveHermitianForm X) :
    ComplexHermitianForm X where
  form := h.form
  conj_symm := h.conj_symm
  add_right := h.add_right
  smul_right := h.smul_right

/-- Precisely a positive-semidefinite Hermitian square for the given seminorm.
Nonnegative diagonal follows from the displayed equality with p². -/
def SeminormIsHilbertian (p : Seminorm ℂ X) : Prop :=
  ∃ h : ComplexHermitianForm X, ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ)

theorem complexPolar_eq_zero_of_seminorm_zero (p : Seminorm ℂ X)
    (x y : X) (hx : p x = 0) : complexPolar p x y = 0 := by
  have hqx : seminormQuotientMap p x = 0 := norm_eq_zero.mp (by rw [seminormQuotientMap_norm, hx])
  have hadd (z : X) : p (x + z) = p z := by
    rw [← seminormQuotientMap_norm, map_add, hqx, zero_add, seminormQuotientMap_norm]
  have hsub (z : X) : p (x - z) = p z := by
    rw [← seminormQuotientMap_norm, map_sub, hqx, zero_sub, norm_neg, seminormQuotientMap_norm]
  simp only [complexPolar, hadd, hsub, sub_self, zero_mul, add_zero, zero_div]

theorem ComplexHermitianForm.eq_zero_of_seminorm_zero (h : ComplexHermitianForm X)
    (p : Seminorm ℂ X) (hdiag : ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ))
    (x y : X) (hx : p x = 0) : h.form x y = 0 := by
  rw [h.eq_complexPolar hdiag]
  exact complexPolar_eq_zero_of_seminorm_zero p x y hx

theorem ComplexHermitianForm.eq_zero_of_seminorm_zero_right (h : ComplexHermitianForm X)
    (p : Seminorm ℂ X) (hdiag : ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ))
    (x y : X) (hy : p y = 0) : h.form x y = 0 := by
  rw [← h.conj_symm y x, h.eq_zero_of_seminorm_zero p hdiag y x hy, star_zero]

theorem ComplexHermitianForm.seminorm_zero_iff_left_radical (h : ComplexHermitianForm X)
    (p : Seminorm ℂ X) (hdiag : ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ)) (x : X) :
    p x = 0 ↔ ∀ y, h.form x y = 0 := by
  constructor
  · intro hx y; exact h.eq_zero_of_seminorm_zero p hdiag x y hx
  · intro hx
    have hp2 : p x ^ 2 = 0 := by
      have hr := congrArg Complex.re ((hdiag x).symm.trans (hx x))
      simpa only [Complex.ofReal_re, Complex.zero_re] using hr
    exact sq_eq_zero_iff.mp hp2

theorem ComplexHermitianForm.congr_of_seminormQuotientMap_eq (h : ComplexHermitianForm X)
    (p : Seminorm ℂ X) (hdiag : ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ))
    (x₁ x₂ y₁ y₂ : X)
    (hx : seminormQuotientMap p x₁ = seminormQuotientMap p x₂)
    (hy : seminormQuotientMap p y₁ = seminormQuotientMap p y₂) :
    h.form x₁ y₁ = h.form x₂ y₂ := by
  have hpx : p (x₁ - x₂) = 0 := by rw [← seminormQuotientMap_norm, map_sub, hx, sub_self, norm_zero]
  have hpy : p (y₁ - y₂) = 0 := by rw [← seminormQuotientMap_norm, map_sub, hy, sub_self, norm_zero]
  have hleft : h.form x₁ y₁ = h.form x₂ y₁ := sub_eq_zero.mp (by
    rw [← h.sub_left]; exact h.eq_zero_of_seminorm_zero p hdiag _ _ hpx)
  have hright : h.form x₂ y₁ = h.form x₂ y₂ := sub_eq_zero.mp (by
    rw [← h.sub_right]; exact h.eq_zero_of_seminorm_zero_right p hdiag _ _ hpy)
  exact hleft.trans hright

def ComplexHermitianForm.seminormQuotient (h : ComplexHermitianForm X)
    (p : Seminorm ℂ X) (hdiag : ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ)) :
    ComplexHermitianForm (SeminormQuotient p) where
  form := SeparationQuotient.lift₂ (fun x y : SeminormModel p => h.form (x : X) (y : X)) (by
    intro x₁ x₂ y₁ y₂ hx hy
    apply h.congr_of_seminormQuotientMap_eq p hdiag
    · exact (hx.map (SeparationQuotient.mkCLM ℂ (SeminormModel p)).continuous).eq
    · exact (hy.map (SeparationQuotient.mkCLM ℂ (SeminormModel p)).continuous).eq)
  conj_symm x y := Quotient.ind₂ (fun a b => h.conj_symm a b) x y
  add_right x y z := by
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    refine Quotient.inductionOn z ?_
    intro c
    exact h.add_right a b c
  smul_right x y a := Quotient.ind₂ (fun v w => h.smul_right v w a) x y

@[simp] theorem ComplexHermitianForm.seminormQuotient_apply
    (h : ComplexHermitianForm X) (p : Seminorm ℂ X)
    (hdiag : ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ)) (x y : X) :
    (h.seminormQuotient p hdiag).form (seminormQuotientMap p x) (seminormQuotientMap p y) =
      h.form x y := rfl

def ComplexHermitianForm.toPositiveForNorm {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (h : ComplexHermitianForm V)
    (hdiag : ∀ x, h.form x x = ((‖x‖ ^ 2 : ℝ) : ℂ)) : PositiveHermitianForm V where
  form := h.form
  conj_symm := h.conj_symm
  add_right := h.add_right
  smul_right := h.smul_right
  self_im x := by rw [hdiag]; exact Complex.ofReal_im _
  self_nonneg x := by rw [hdiag, Complex.ofReal_re]; exact sq_nonneg _
  self_pos x hx := by rw [hdiag, Complex.ofReal_re]; exact sq_pos_iff.mpr (norm_ne_zero_iff.mpr hx)

theorem quotient_hasHermitianSquare_of_seminormIsHilbertian (p : Seminorm ℂ X)
    (hp : SeminormIsHilbertian p) : HasHermitianSquare (norm : SeminormQuotient p → ℝ) := by
  obtain ⟨h, hdiag⟩ := hp
  let hQ := h.seminormQuotient p hdiag
  have hQdiag : ∀ z : SeminormQuotient p, hQ.form z z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective p z
    rw [seminormQuotientMap_norm]
    exact hdiag x
  exact ⟨hQ.toPositiveForNorm hQdiag, hQdiag⟩

theorem seminormIsHilbertian_of_quotient_square (p : Seminorm ℂ X)
    (hp : HasHermitianSquare (norm : SeminormQuotient p → ℝ)) : SeminormIsHilbertian p := by
  obtain ⟨h, hdiag⟩ := hp
  refine ⟨h.toComplexHermitianForm.comap (seminormQuotientMap p), ?_⟩
  intro x
  change h.form (seminormQuotientMap p x) (seminormQuotientMap p x) = _
  simpa only [seminormQuotientMap_norm] using hdiag (seminormQuotientMap p x)

theorem seminormIsHilbertian_iff_quotient_square (p : Seminorm ℂ X) :
    SeminormIsHilbertian p ↔ HasHermitianSquare (norm : SeminormQuotient p → ℝ) :=
  ⟨quotient_hasHermitianSquare_of_seminormIsHilbertian p, seminormIsHilbertian_of_quotient_square p⟩

end BanachIsometric
