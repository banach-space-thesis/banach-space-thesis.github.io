import JLMS.CompetingNorms
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Completing an arbitrary algebra norm

Equip a unital algebra with a supplied submultiplicative vector norm, then
embed it in its Banach completion as an algebra homomorphism. Automatic
continuity of homomorphisms from the original algebra consequently bounds
every competing algebra norm from above, without assuming its completeness.
-/

noncomputable section
set_option maxHeartbeats 1500000
namespace JLMS
open UniformSpace
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {B : Type u} [NormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]

def withAlgebraNormRing {B : Type*} [Ring B] [Module 𝕜 B]
    (n : B → ℝ) (hn : IsAlgebraNorm 𝕜 n) :
    NormedRing (WithVectorNorm 𝕜 n hn.1) where
  __ := withVectorNormGroup 𝕜 n hn.1
  __ := inferInstanceAs (Ring B)
  norm_mul_le x y := hn.2 x y

instance completionScalarTower : IsScalarTower 𝕜 (Completion B) (Completion B) where
  smul_assoc c x y := by
    change (c • x) * y = c • (x * y)
    induction x, y using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq
        (((continuous_const_smul c).comp continuous_fst).mul continuous_snd)
        ((continuous_const_smul c).comp (continuous_fst.mul continuous_snd))
    | ih x y =>
      simpa only [← Completion.coe_mul, ← Completion.coe_smul] using
        congrArg (fun z : B => (z : Completion B)) (smul_mul_assoc c x y)

instance completionScalarComm : SMulCommClass 𝕜 (Completion B) (Completion B) where
  smul_comm c x y := by
    change c • (x * y) = x * (c • y)
    induction x, y using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq
        ((continuous_const_smul c).comp (continuous_fst.mul continuous_snd))
        (continuous_fst.mul ((continuous_const_smul c).comp continuous_snd))
    | ih x y =>
      simpa only [← Completion.coe_mul, ← Completion.coe_smul] using
        congrArg (fun z : B => (z : Completion B)) (mul_smul_comm c x y).symm

theorem algebraNorm_bound_of_hom_automaticContinuity
    (hB : ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
      [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
      ∀ φ : B →ₙₐ[𝕜] A, Continuous φ)
    {Q : Type u} [Ring Q] [Module 𝕜 Q]
    [IsScalarTower 𝕜 Q Q] [SMulCommClass 𝕜 Q Q]
    (q : B →ₙₐ[𝕜] Q) (n : Q → ℝ) (hn : IsAlgebraNorm 𝕜 n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, n (q x) ≤ C * ‖x‖ := by
  let V := WithVectorNorm 𝕜 n hn.1
  letI : NormedRing V := withAlgebraNormRing n hn
  letI : IsScalarTower 𝕜 V V := inferInstanceAs (IsScalarTower 𝕜 Q Q)
  letI : SMulCommClass 𝕜 V V := inferInstanceAs (SMulCommClass 𝕜 Q Q)
  let N := ULift.{0} V
  letI : IsScalarTower 𝕜 N N := {
    smul_assoc := fun c x y => by
      apply ULift.ext
      exact smul_mul_assoc c x.down y.down
  }
  letI : SMulCommClass 𝕜 N N := {
    smul_comm := fun c x y => by
      apply ULift.ext
      exact (mul_smul_comm c x.down y.down).symm
  }
  let ψ : Q →ₙₐ[𝕜] Completion N := {
    toFun := fun x => ((ULift.up (x : V) : N) : Completion N)
    map_zero' := Completion.coe_zero
    map_add' := fun x y => Completion.coe_add (ULift.up x : N) (ULift.up y : N)
    map_mul' := fun x y => Completion.coe_mul (ULift.up x : N) (ULift.up y : N)
    map_smul' := fun c x => Completion.coe_smul c (ULift.up x : N)
  }
  let φ := ψ.comp q
  have hφ := hB (Completion N) φ
  let L : B →L[𝕜] Completion N := {
    toLinearMap := {
      toFun := φ
      map_add' := φ.map_add
      map_smul' := φ.map_smul
    }
    cont := hφ
  }
  refine ⟨‖L‖ + 1, by positivity, fun x => ?_⟩
  have hh := L.le_opNorm x
  change ‖((ULift.up (q x : V) : N) : Completion N)‖ ≤ _ at hh
  rw [Completion.norm_coe] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))

theorem algebraNorm_upper_bound_of_automaticContinuity
    (hB : ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
      [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
      ∀ φ : B →ₙₐ[𝕜] A, Continuous φ)
    (n : B → ℝ) (hn : IsAlgebraNorm 𝕜 n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, n x ≤ C * ‖x‖ :=
  algebraNorm_bound_of_hom_automaticContinuity hB (NonUnitalAlgHom.id 𝕜 B) n hn

end JLMS
