import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The ordinary quotient norm makes the quotient by a closed two-sided
ideal in a noncommutative normed algebra into a normed algebra. -/

noncomputable section
open Filter Metric Set Topology
namespace ThesisCommon

variable {A : Type*} [NormedRing A] (I : Ideal A) [I.IsTwoSided]

/-- The standard quotient norm is submultiplicative; commutativity of the
ambient algebra is unnecessary. -/
theorem noncommutativeQuotient_norm_mul_le (x y : A ⧸ I) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
    (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
  simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall, Prod.exists] at h
  obtain ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩ := h
  obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x h₁
  obtain ⟨b, rfl, hb⟩ := Submodule.Quotient.norm_mk_lt y h₂
  simp only [dist, abs_sub_lt_iff] at h
  specialize h ‖a‖ ‖b‖
    ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le I a]⟩
    ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le I b]⟩
  calc
    _ ≤ ‖a‖ * ‖b‖ := (Submodule.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
    _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

/-- This reuses the existing normed additive quotient, preserving its metric
and norm exactly. The low priority leaves mathlib's commutative instances in place. -/
instance (priority := 100) noncommutativeQuotientNormedRing [IsClosed (I : Set A)] :
    NormedRing (A ⧸ I) where
  __ := (inferInstance : Ring (A ⧸ I))
  __ := (inferInstance : NormedAddCommGroup (A ⧸ I))
  norm_mul_le := noncommutativeQuotient_norm_mul_le I

instance (priority := 100) noncommutativeQuotientNormedAlgebra
    (𝕜 : Type*) [NormedField 𝕜] [NormedAlgebra 𝕜 A] [IsClosed (I : Set A)] :
    NormedAlgebra 𝕜 (A ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }

end ThesisCommon
