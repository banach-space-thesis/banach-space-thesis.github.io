import AutomaticContinuity.CorollaryBStatement
import AutomaticContinuity.TheoremA
import AutomaticContinuity.Characters
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded

set_option autoImplicit false

namespace AutomaticContinuity

open Filter
open scoped Topology

universe u

variable {A : Type u} [NonUnitalCommRing A] [Module ℂ A]

/-- Forget multiplication, retaining the character's complex linearity. -/
def characterLinearMap (χ : A →ₙₐ[ℂ] ℂ) : A →ₗ[ℂ] ℂ where
  toFun := χ
  map_add' := map_add χ
  map_smul' := fun c a => map_smul χ c a

/-- The power argument removes the multiplicative constant, without adjoining
an identity. Positive powers are represented by an explicit recursion. -/
theorem character_le_seminorm_of_bound (χ : A →ₙₐ[ℂ] ℂ)
    (p : Seminorm ℂ A) (hp : IsSubmultiplicative A p)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ a, ‖χ a‖ ≤ C * p a) :
    ∀ a, ‖χ a‖ ≤ p a := by
  intro a
  by_contra! ha
  have hnorm : 0 < ‖χ a‖ := (apply_nonneg p a).trans_lt ha
  have hne : χ a ≠ 0 := norm_pos_iff.mp hnorm
  let b : A := (χ a)⁻¹ • a
  have hb : χ b = 1 := by simp [b, hne]
  have hpb : p b < 1 := by
    simp only [b, map_smul_eq_mul, norm_inv]
    rw [inv_mul_lt_iff₀ hnorm]
    simpa using ha
  let v : ℕ → A := Nat.rec b (fun _ x => b * x)
  have hvχ : ∀ n, χ (v n) = 1 := by
    intro n
    induction n with
    | zero => exact hb
    | succ n ih => simpa [v, map_mul, hb] using ih
  have hvp : ∀ n, p (v n) ≤ p b ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp [v]
    | succ n ih =>
      calc
        p (v (n + 1)) ≤ p b * p (v n) := hp b (v n)
        _ ≤ p b * p b ^ (n + 1) := mul_le_mul_of_nonneg_left ih (apply_nonneg p b)
        _ = p b ^ (n + 1 + 1) := (pow_succ' _ _).symm
  have hle : ∀ n, (1 : ℝ) ≤ C * p b ^ (n + 1) := by
    intro n
    have h := (hbound (v n)).trans (mul_le_mul_of_nonneg_left (hvp n) hC)
    simpa [hvχ n] using h
  have ht : Tendsto (fun n : ℕ => C * p b ^ (n + 1)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (apply_nonneg p b) hpb).comp
      (tendsto_add_atTop_nat 1)).const_mul C
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hle)
  norm_num at this

theorem continuous_character_le_defining_seminorm [TopologicalSpace A]
    (χ : A →ₙₐ[ℂ] ℂ) (hχ : Continuous χ)
    (p : ℕ → Seminorm ℂ A) (hmono : Monotone p)
    (hmul : ∀ n, IsSubmultiplicative A (p n)) (htop : WithSeminorms p) :
    ∃ n : ℕ, ∀ a, ‖χ a‖ ≤ p n a := by
  let q : Seminorm ℂ A := (normSeminorm ℂ ℂ).comp (characterLinearMap χ)
  have hq : Continuous q := hχ.norm
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous htop q hq
  have hsup : s.sup p ≤ p (s.sup id) :=
    Finset.sup_le (fun n hn => hmono (Finset.le_sup (f := id) hn))
  refine ⟨s.sup id, character_le_seminorm_of_bound χ _ (hmul _) C.coe_nonneg ?_⟩
  intro a
  exact (hC a).trans (mul_le_mul_of_nonneg_left (hsup a) C.coe_nonneg)

theorem corollaryB : CorollaryBStatement.{u} := by
  intro A _ _ _ _ _ _ _ _ _ hA χ
  obtain ⟨P, hsub, hP⟩ := hA
  let := hP.continuousSMul
  have hχ : Continuous χ.val := (characterLinearMap χ.val).continuous_of_locally_bounded
    ((boundedOnBoundedSets_iff_image _).mp (theoremA A ⟨P, hsub, hP⟩ χ))
  exact ⟨hχ, fun p hm hs ht => continuous_character_le_defining_seminorm χ.val hχ p hm hs ht⟩

end AutomaticContinuity
