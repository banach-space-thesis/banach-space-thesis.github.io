import SurveyStatements.P2ShiftMaximalIdeal
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.Linarith

/-! The genuine quotient Banach algebra by a closed two-sided ideal. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace SurveyStatements.P2
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The same quotient classes as the analytic quotient vector space. -/
abbrev IdealQuotient (M : TwoSidedIdeal A) := A ⧸ idealSubmodule M

/-- The ideal relation is compatible with the quotient-vector-space relation. -/
def idealCongruence (M : TwoSidedIdeal A) : RingCon A where
  __ := (idealSubmodule M).quotientRel
  add' := by
    intro s s' t t' hs ht
    simp only [Submodule.quotientRel_def, mem_idealSubmodule] at hs ht ⊢
    exact (M.rel_iff _ _).mp (M.ringCon.add ((M.rel_iff _ _).mpr hs)
      ((M.rel_iff _ _).mpr ht))
  mul' := by
    intro s s' t t' hs ht
    simp only [Submodule.quotientRel_def, mem_idealSubmodule] at hs ht ⊢
    exact (M.rel_iff _ _).mp (M.ringCon.mul ((M.rel_iff _ _).mpr hs)
      ((M.rel_iff _ _).mpr ht))

instance idealQuotientRing (M : TwoSidedIdeal A) : Ring (IdealQuotient M) :=
  inferInstanceAs (Ring (idealCongruence M).Quotient)

def idealQuotientMap (M : TwoSidedIdeal A) : A →ₗ[ℂ] IdealQuotient M :=
  (idealSubmodule M).mkQ

@[simp] theorem idealQuotientMap_mul (M : TwoSidedIdeal A) (s t : A) :
    idealQuotientMap M (s * t) = idealQuotientMap M s * idealQuotientMap M t := rfl

@[simp] theorem idealQuotientMap_one (M : TwoSidedIdeal A) :
    idealQuotientMap M 1 = (1 : IdealQuotient M) := rfl

@[simp] theorem idealQuotientMap_eq_zero (M : TwoSidedIdeal A) (s : A) :
    idealQuotientMap M s = 0 ↔ s ∈ M := Submodule.Quotient.mk_eq_zero _

theorem idealQuotientMap_surjective (M : TwoSidedIdeal A) :
    Function.Surjective (idealQuotientMap M) := Submodule.mkQ_surjective _

instance idealQuotientScalarTower (M : TwoSidedIdeal A) :
    IsScalarTower ℂ (IdealQuotient M) (IdealQuotient M) where
  smul_assoc c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H s =>
      induction y using Submodule.Quotient.induction_on with
      | H t => exact congrArg (idealQuotientMap M) (smul_mul_assoc c s t)

instance idealQuotientScalarComm (M : TwoSidedIdeal A) :
    SMulCommClass ℂ (IdealQuotient M) (IdealQuotient M) where
  smul_comm c x y := by
    induction x using Submodule.Quotient.induction_on with
    | H s =>
      induction y using Submodule.Quotient.induction_on with
      | H t => exact congrArg (idealQuotientMap M) (mul_smul_comm c s t).symm

instance idealQuotientAlgebra (M : TwoSidedIdeal A) : Algebra ℂ (IdealQuotient M) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- Approximate lifts prove the submultiplicativity of the actual quotient norm. -/
theorem idealQuotient_norm_mul_le (M : TwoSidedIdeal A) (x y : IdealQuotient M) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ :=
  le_of_forall_pos_le_add fun ε hε => by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) (‖x‖, ‖y‖) :=
      continuous_mul.continuousAt
    obtain ⟨δ, hδ, hδbound⟩ := (Metric.tendsto_nhds_nhds.mp hcont.tendsto) ε hε
    obtain ⟨s, hs, hns⟩ := Submodule.Quotient.norm_mk_lt x hδ
    obtain ⟨t, ht, hnt⟩ := Submodule.Quotient.norm_mk_lt y hδ
    have hlows : ‖x‖ ≤ ‖s‖ := by
      simpa only [← hs] using Submodule.Quotient.norm_mk_le (idealSubmodule M) s
    have hlowt : ‖y‖ ≤ ‖t‖ := by
      simpa only [← ht] using Submodule.Quotient.norm_mk_le (idealSubmodule M) t
    have hp : dist (‖s‖, ‖t‖) (‖x‖, ‖y‖) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      rw [abs_sub_lt_iff, abs_sub_lt_iff]
      constructor <;> constructor <;> linarith
    have hproduct := hδbound hp
    rw [Real.dist_eq, abs_sub_lt_iff] at hproduct
    calc
      ‖x * y‖ = ‖idealQuotientMap M (s * t)‖ := by
        rw [idealQuotientMap_mul]
        exact congrArg norm (congrArg₂ (· * ·) hs ht).symm
      _ ≤ ‖s * t‖ := Submodule.Quotient.norm_mk_le (idealSubmodule M) _
      _ ≤ ‖s‖ * ‖t‖ := norm_mul_le _ _
      _ ≤ ‖x‖ * ‖y‖ + ε := by linarith [hproduct.1]

instance idealQuotientSeminormedRing (M : TwoSidedIdeal A) :
    SeminormedRing (IdealQuotient M) :=
  { idealQuotientRing M, (inferInstance : SeminormedAddCommGroup (IdealQuotient M)) with
    norm_mul_le := idealQuotient_norm_mul_le M }

instance idealQuotientNormedRing (M : TwoSidedIdeal A) [Fact (IsClosed (M : Set A))] :
    NormedRing (IdealQuotient M) :=
  { idealQuotientSeminormedRing M, (inferInstance : NormedAddCommGroup (IdealQuotient M)) with }

instance idealQuotientNormedAlgebra (M : TwoSidedIdeal A) :
    NormedAlgebra ℂ (IdealQuotient M) :=
  { idealQuotientAlgebra M, (inferInstance : NormedSpace ℂ (IdealQuotient M)) with }

/-- The quotient map with its actual complex algebra structure. -/
def idealQuotientAlgHom (M : TwoSidedIdeal A) : A →ₐ[ℂ] IdealQuotient M :=
  AlgHom.ofLinearMap (idealQuotientMap M) (idealQuotientMap_one M)
    (idealQuotientMap_mul M)

/-- Algebraic simplicity of a quotient by a maximal proper two-sided ideal. -/
theorem idealQuotient_simple (M : TwoSidedIdeal A) (hM : IsCoatom M)
    (J : TwoSidedIdeal (IdealQuotient M)) : J = ⊥ ∨ J = ⊤ := by
  let q := (idealQuotientAlgHom M).toRingHom
  let K := J.comap q
  have hMK : M ≤ K := by
    intro x hx
    apply (TwoSidedIdeal.mem_comap q).mpr
    have hzero : q x = 0 := (idealQuotientMap_eq_zero M x).mpr hx
    rw [hzero]
    exact J.zero_mem
  by_cases hK : K = ⊤
  · right
    apply J.eq_top
    have h1 : (1 : A) ∈ K := by rw [hK]; trivial
    simpa only [TwoSidedIdeal.mem_comap, map_one] using h1
  · left
    have hKM : K = M := le_antisymm ((isCoatom_iff_ge_of_le.mp hM).2 K hK hMK) hMK
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, rfl⟩ := idealQuotientMap_surjective M y
    have hx : x ∈ K := (TwoSidedIdeal.mem_comap q).mpr hy
    have hz : idealQuotientMap M x = 0 := (idealQuotientMap_eq_zero M x).mpr (hKM ▸ hx)
    simpa only [TwoSidedIdeal.mem_bot] using hz

end SurveyStatements.P2
