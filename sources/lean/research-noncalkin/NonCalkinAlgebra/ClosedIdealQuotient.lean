import NonCalkinAlgebra.CStarIdeals
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u
namespace ClosedIdealQuotient
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

/-- The complex submodule underlying an actual two-sided ring ideal. -/
def submodule (I : TwoSidedIdeal A) : Submodule ℂ A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro c a ha
    rw [Algebra.smul_def]
    exact I.mul_mem_left (algebraMap ℂ A c) a ha

variable (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
instance submodule_isClosed : IsClosed (submodule I : Set A) :=
  inferInstanceAs (IsClosed (I : Set A))

abbrev Space := A ⧸ submodule I

def q : A →ₗ[ℂ] Space I := (submodule I).mkQ
def congruence  : RingCon (A) where
  __ := (submodule I).quotientRel
  add' := by
    intro S S' T T' hS hT
    rw [Submodule.quotientRel_def] at hS hT ⊢
    have h := (submodule I).add_mem hS hT
    convert h using 1
    abel
  mul' := by
    intro S S' T T' hS hT
    rw [Submodule.quotientRel_def] at hS hT ⊢
    have h := (submodule I).add_mem
      (I.mul_mem_right (S - S') T hS)
      (I.mul_mem_left S' (T - T') hT)
    convert h using 1
    noncomm_ring

instance quotientRing  :
    Ring (Space I) :=
  inferInstanceAs (Ring (congruence I).Quotient)

@[simp] theorem q_mul 
    (S T : A) :
    q I (S * T) =
      q I S * q I T := rfl

@[simp] theorem q_one  :
    q I 1 = (1 : Space I) := rfl

@[simp] theorem q_eq_zero 
    (T : A) :
    q I T = 0 ↔ T ∈ submodule I :=
  Submodule.Quotient.mk_eq_zero _

theorem q_surjective  :
    Function.Surjective (q I) :=
  Submodule.mkQ_surjective _

instance quotientScalarTower  :
    IsScalarTower ℂ (Space I) (Space I) where
  smul_assoc c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T => exact congrArg (q I) (smul_mul_assoc c S T)

instance quotientScalarComm  :
    SMulCommClass ℂ (Space I) (Space I) where
  smul_comm c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T => exact congrArg (q I) (mul_smul_comm c S T).symm

instance quotientAlgebra  :
    Algebra ℂ (Space I) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem quotient_norm_mul_le 
    (x y : Space I) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  le_of_forall_pos_le_add fun ε hε => by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) (‖x‖, ‖y‖) :=
      continuous_mul.continuousAt
    obtain ⟨δ, hδ, hδbound⟩ := (Metric.tendsto_nhds_nhds.mp hcont.tendsto) ε hε
    obtain ⟨S, hS, hnS⟩ := Submodule.Quotient.norm_mk_lt x hδ
    obtain ⟨T, hT, hnT⟩ := Submodule.Quotient.norm_mk_lt y hδ
    have hlowS : ‖x‖ ≤ ‖S‖ := by
      simpa only [← hS] using Submodule.Quotient.norm_mk_le (submodule I) S
    have hlowT : ‖y‖ ≤ ‖T‖ := by
      simpa only [← hT] using Submodule.Quotient.norm_mk_le (submodule I) T
    have hp : dist (‖S‖, ‖T‖) (‖x‖, ‖y‖) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      rw [abs_sub_lt_iff, abs_sub_lt_iff]
      constructor <;> constructor <;> linarith
    have hproduct := hδbound hp
    rw [Real.dist_eq, abs_sub_lt_iff] at hproduct
    calc
      ‖x * y‖ = ‖q I (S * T)‖ := by
        rw [q_mul]
        exact congrArg norm (congrArg₂ (· * ·) hS hT).symm
      _ ≤ ‖S * T‖ := Submodule.Quotient.norm_mk_le (submodule I) _
      _ ≤ ‖S‖ * ‖T‖ := norm_mul_le _ _
      _ ≤ ‖x‖ * ‖y‖ + ε := by linarith [hproduct.1]

instance quotientSeminormedRing  :
    SeminormedRing (Space I) :=
  { quotientRing I,
      (inferInstance : SeminormedAddCommGroup (Space I)) with
    norm_mul_le := quotient_norm_mul_le I }

instance quotientNormedRing  :
    NormedRing (Space I) :=
  { quotientSeminormedRing I,
      (inferInstance : NormedAddCommGroup (Space I)) with }

instance quotientNormedAlgebra  :
    NormedAlgebra ℂ (Space I) :=
  { quotientAlgebra I,
      (inferInstance : NormedSpace ℂ (Space I)) with }

def qCLM : A →L[ℂ] Space I :=
  (q I).mkContinuous 1 (fun (a : A) => by
    simpa only [one_mul] using (Submodule.Quotient.norm_mk_le (submodule I) a))

def qAlgHom : A →ₐ[ℂ] Space I where
  toFun := q I
  map_zero' := map_zero (q I)
  map_add' := map_add (q I)
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, q_one,
      Algebra.algebraMap_eq_smul_one]

instance quotientCompleteSpace [CompleteSpace A] : CompleteSpace (Space I) := inferInstance

theorem quotient_nontrivial (hne : I ≠ ⊤) : Nontrivial (Space I) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have h1 : (1 : A) ∈ I := (q_eq_zero I 1).mp h
  exact hne (I.one_mem_iff.mp h1)

instance quotientNormOneClass [NormOneClass A] [Nontrivial (Space I)] :
    NormOneClass (Space I) where
  norm_one := le_antisymm (by simpa only [q_one, norm_one] using
    Submodule.Quotient.norm_mk_le (submodule I) (1 : A)) (one_le_norm_one _)

end ClosedIdealQuotient

namespace ClosedIdealQuotient
variable {A : Type u} [CStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- The quotient involution uses the proved automatic self-adjointness of I. -/
instance quotientStar : Star (Space I) where
  star := Quotient.map' star (by
    intro x y hxy
    rw [Submodule.quotientRel_def] at hxy ⊢
    exact (by simpa only [star_sub] using
      closed_twoSidedIdeal_star_mem I (inferInstance : IsClosed (I : Set A)) hxy))

@[simp] theorem star_q (a : A) : star (q I a) = q I (star a) := rfl

instance quotientStarRing : StarRing (Space I) where
  star_involutive z := by
    induction z using Submodule.Quotient.induction_on with
    | H a =>
      change q I (star (star a)) = q I a
      exact congrArg (q I) (star_star a)
  star_mul z w := by
    induction z using Submodule.Quotient.induction_on with
    | H a =>
      induction w using Submodule.Quotient.induction_on with
      | H b =>
        change q I (star (a * b)) = q I (star b * star a)
        exact congrArg (q I) (star_mul a b)
  star_add z w := by
    induction z using Submodule.Quotient.induction_on with
    | H a =>
      induction w using Submodule.Quotient.induction_on with
      | H b =>
        change q I (star (a + b)) = q I (star a + star b)
        exact congrArg (q I) (star_add a b)

instance quotientNormedStarGroup : NormedStarGroup (Space I) where
  norm_star_le z := le_of_forall_pos_le_add fun ε hε => by
    obtain ⟨a, ha, hnorm⟩ := Submodule.Quotient.norm_mk_lt z hε
    calc
      ‖star z‖ = ‖q I (star a)‖ := by rw [← ha]; rfl
      _ ≤ ‖star a‖ := Submodule.Quotient.norm_mk_le (submodule I) _
      _ = ‖a‖ := norm_star _
      _ ≤ ‖z‖ + ε := hnorm.le

def qStarAlgHom : A →⋆ₐ[ℂ] Space I where
  __ := qAlgHom I
  map_star' := fun _ => rfl

end ClosedIdealQuotient
end NonCalkinAlgebra
