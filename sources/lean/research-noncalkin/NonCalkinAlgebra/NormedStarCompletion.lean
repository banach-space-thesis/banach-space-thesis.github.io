import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Module.Completion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.NormedStarCompletion
open UniformSpace
universe u
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

scoped instance completionAlgebra : Algebra ℂ (Completion A) :=
  Algebra.ofModule
    (fun c x y => Completion.induction_on₂ x y
      (isClosed_eq ((continuous_const.smul continuous_fst).mul continuous_snd)
        (continuous_const.smul continuous_mul))
      (fun a b => by
        simp only [← Completion.coe_smul, ← Completion.coe_mul, smul_mul_assoc]))
    (fun c x y => Completion.induction_on₂ x y
      (isClosed_eq (continuous_fst.mul (continuous_const.smul continuous_snd))
        (continuous_const.smul continuous_mul))
      (fun a b => by
        simp only [← Completion.coe_smul, ← Completion.coe_mul, mul_smul_comm]))

scoped instance completionNormedAlgebra : NormedAlgebra ℂ (Completion A) where
  norm_smul_le := norm_smul_le

variable [StarRing A] [NormedStarGroup A]

def completionStar : Completion A → Completion A := Completion.map (star : A → A)

theorem continuous_completionStar : Continuous (completionStar (A := A)) :=
  Completion.continuous_map

@[simp] theorem completionStar_coe (a : A) :
    completionStar (a : Completion A) = (star a : A) :=
  Completion.map_coe star_isometry.uniformContinuous a

scoped instance completionStarRing : StarRing (Completion A) where
  star := completionStar
  star_involutive := fun x => Completion.induction_on x
    (isClosed_eq (continuous_completionStar.comp continuous_completionStar) continuous_id)
    (fun a => by simp only [completionStar_coe, star_star])
  star_mul := fun x y => Completion.induction_on₂ x y
    (isClosed_eq (continuous_completionStar.comp (by fun_prop))
      ((continuous_completionStar.comp continuous_snd).mul
        (continuous_completionStar.comp continuous_fst)))
    (fun a b => by simp only [← Completion.coe_mul, completionStar_coe, star_mul])
  star_add := fun x y => Completion.induction_on₂ x y
    (isClosed_eq (continuous_completionStar.comp (by fun_prop))
      ((continuous_completionStar.comp continuous_fst).add
        (continuous_completionStar.comp continuous_snd)))
    (fun a b => by simp only [← Completion.coe_add, completionStar_coe, star_add])

@[simp] theorem star_coe (a : A) : star (a : Completion A) = (star a : A) :=
  completionStar_coe a

scoped instance completionStarModule [StarModule ℂ A] : StarModule ℂ (Completion A) where
  star_smul c x := Completion.induction_on x
    (isClosed_eq (continuous_completionStar.comp (by fun_prop))
      (continuous_const.smul continuous_completionStar))
    (fun a => by simp only [← Completion.coe_smul, star_coe, star_smul])

scoped instance completionNormedStarGroup : NormedStarGroup (Completion A) where
  norm_star_le x := Completion.induction_on x
    (isClosed_le (continuous_norm.comp continuous_completionStar) continuous_norm)
    (fun a => by simp only [star_coe, Completion.norm_coe, norm_star, le_refl])

/-- The C* identity extends from a normed *-algebra to its actual completion. -/
scoped instance completionCStarRing [CStarRing A] : CStarRing (Completion A) where
  norm_mul_self_le x := Completion.induction_on x
    (isClosed_le (continuous_norm.mul continuous_norm)
      (continuous_norm.comp (continuous_completionStar.mul continuous_id)))
    (fun a => by
      simp only [star_coe, ← Completion.coe_mul, Completion.norm_coe,
        CStarRing.norm_star_mul_self, le_refl])

end NonCalkinAlgebra.NormedStarCompletion
