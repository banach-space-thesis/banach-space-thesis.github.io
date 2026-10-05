import ThesisCommon.Analysis.SigmaComplexLatticeModulus
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Prod

/-! General complex Banach lattices, specified by their real vector lattice,
complexification coordinates, and intrinsic modulus. No function-space
representation or atomicity is built into the definition. -/
noncomputable section
universe u
namespace ThesisCommon

structure ComplexBanachLattice where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace ℂ Carrier]
  [completeSpace : CompleteSpace Carrier]
  RealPart : RealBanachLattice.{u}
  coordinates : Carrier ≃L[ℝ] (RealPart × RealPart)
  coordinates_I : ∀ z, coordinates (Complex.I • z) = (-(coordinates z).2,(coordinates z).1)
  modulus : Carrier → RealPart
  modulus_spec : ∀ z, IsComplexLatticeModulus (coordinates z).1 (coordinates z).2 (modulus z)
  norm_modulus : ∀ z, ‖z‖ = ‖modulus z‖

attribute [instance] ComplexBanachLattice.normedAddCommGroup ComplexBanachLattice.normedSpace
  ComplexBanachLattice.completeSpace
instance : CoeSort ComplexBanachLattice (Type u) := ⟨ComplexBanachLattice.Carrier⟩

/-- All complex Banach lattices, allowing arbitrary Banach-space isomorphisms. -/
def IsomorphicToComplexBanachLattice (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℂ E] : Prop :=
  ∃ F : ComplexBanachLattice.{u}, Nonempty (E ≃L[ℂ] F)

namespace ComplexBanachLattice
variable (F : ComplexBanachLattice.{u})

def re : F →L[ℝ] F.RealPart :=
  (ContinuousLinearMap.fst ℝ _ _).comp F.coordinates.toContinuousLinearMap

def im : F →L[ℝ] F.RealPart :=
  (ContinuousLinearMap.snd ℝ _ _).comp F.coordinates.toContinuousLinearMap

@[simp] theorem re_apply (z : F) : F.re z = (F.coordinates z).1 := rfl
@[simp] theorem im_apply (z : F) : F.im z = (F.coordinates z).2 := rfl

@[simp] theorem re_I (z : F) : F.re (Complex.I • z) = -F.im z := by
  simp only [re_apply,im_apply,F.coordinates_I]

@[simp] theorem im_I (z : F) : F.im (Complex.I • z) = F.re z := by
  simp only [re_apply,im_apply,F.coordinates_I]

def ofReal : F.RealPart →L[ℝ] F :=
  F.coordinates.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

@[simp] theorem re_ofReal (x : F.RealPart) : F.re (F.ofReal x) = x := by
  change (F.coordinates (F.coordinates.symm (x,0))).1 = x
  simp

@[simp] theorem im_ofReal (x : F.RealPart) : F.im (F.ofReal x) = 0 := by
  change (F.coordinates (F.coordinates.symm (x,0))).2 = 0
  simp

theorem re_norm_le (z : F) : ‖F.re z‖ ≤ ‖z‖ := by
  rw [F.norm_modulus z]
  exact norm_le_norm_of_abs_le_abs ((F.modulus_spec z).abs_fst_le.trans_eq
    (abs_of_nonneg (F.modulus_spec z).nonneg).symm)

theorem im_norm_le (z : F) : ‖F.im z‖ ≤ ‖z‖ := by
  rw [F.norm_modulus z]
  exact norm_le_norm_of_abs_le_abs ((F.modulus_spec z).abs_snd_le.trans_eq
    (abs_of_nonneg (F.modulus_spec z).nonneg).symm)

theorem norm_le_re_add_im (z : F) : ‖z‖ ≤ ‖F.re z‖+‖F.im z‖ := by
  rw [F.norm_modulus z]
  calc
    ‖F.modulus z‖ ≤ ‖|F.re z|+|F.im z|‖ :=
      norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg (F.modulus_spec z).nonneg,
          abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
        exact (F.modulus_spec z).le_abs_add)
    _ ≤ ‖|F.re z|‖+‖|F.im z|‖ := norm_add_le _ _
    _ = ‖F.re z‖+‖F.im z‖ := by rw [norm_abs_eq_norm,norm_abs_eq_norm]

/-- The complex-linear extension of a real functional on the real part. -/
def complexifyFunctional (φ : F.RealPart →L[ℝ] ℝ) : F →L[ℂ] ℂ :=
  (φ.comp F.re).extendTo𝕜'

@[simp] theorem complexifyFunctional_apply (φ : F.RealPart →L[ℝ] ℝ) (z : F) :
    F.complexifyFunctional φ z = (⟨φ (F.re z),φ (F.im z)⟩ : ℂ) := by
  rw [complexifyFunctional,ContinuousLinearMap.extendTo𝕜'_apply]
  change (φ (F.re z) : ℂ) - Complex.I * (φ (F.re (Complex.I • z)) : ℂ) = _
  rw [F.re_I,map_neg]
  apply Complex.ext <;> simp

theorem complexifyFunctional_norm_le (φ : F.RealPart →L[ℝ] ℝ) :
    ‖F.complexifyFunctional φ‖ ≤ ‖φ‖ := by
  rw [complexifyFunctional,ContinuousLinearMap.norm_extendTo𝕜']
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (F.re_norm_le z) (norm_nonneg φ))

theorem complexifyFunctional_modulus (φ : F.RealPart →L[ℝ] ℝ)
    (hφ : ∀ x, φ |x| = |φ x|) (z : F) :
    F.complexifyFunctional φ (F.ofReal (F.modulus z)) = (‖F.complexifyFunctional φ z‖ : ℂ) := by
  rw [F.complexifyFunctional_apply,F.re_ofReal,F.im_ofReal,map_zero,
    F.complexifyFunctional_apply]
  have h := (F.modulus_spec z).map_latticeHom φ hφ
  change (⟨φ (F.modulus z),0⟩ : ℂ) = _
  rw [h]
  rfl

end ComplexBanachLattice
end ThesisCommon

