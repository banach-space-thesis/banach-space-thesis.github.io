import SurveyStatements.P5Support.GrothendieckMoments
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Sort

/-! Restricting a uniform finite sign cube to any packet keeps the
uniform sign distribution on that packet, including the empty packet. -/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support.Grothendieck

theorem mean_instance_congr {A : Type*} (t₁ t₂ : Fintype A)
    (f g : A → ℝ) (h : f = g) : @mean A t₁ f = @mean A t₂ g := by
  cases Subsingleton.elim t₁ t₂
  cases h
  rfl

theorem mean_reindex {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : mean (fun a => f (e a)) = mean f := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem mean_product_first {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → ℝ) : mean (fun x : A × B => f x.1) = mean f := by
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold mean
  rw [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rw [mul_inv_rev]
  calc
    _ = ((Fintype.card B : ℝ)⁻¹ * Fintype.card B) *
        ((Fintype.card A : ℝ)⁻¹ * ∑ a, f a) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hB, one_mul]

theorem mean_sign_restrict_subtype {I : Type*} [Fintype I]
    (S : Finset I) (f : (S → Bool) → ℝ) :
    mean (fun θ : I → Bool => f (fun i => θ i.val)) = mean f := by
  let e := Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => Bool)
  calc
    _ = mean (fun x : (S → Bool) × ({i : I // i ∉ S} → Bool) => f x.1) :=
      mean_reindex e (fun x => f x.1)
    _ = _ := mean_product_first f

theorem mean_sign_restrict_packet {n : ℕ} (S : Finset (Fin n))
    (f : (Fin S.card → Bool) → ℝ) :
    mean (fun θ : Fin n → Bool =>
      f (fun i => θ (S.orderEmbOfFin rfl i))) = mean f := by
  let e : Fin S.card ≃ S := (S.orderIsoOfFin rfl).toEquiv
  let a : (S → Bool) ≃ (Fin S.card → Bool) :=
    Equiv.arrowCongr e.symm (Equiv.refl Bool)
  have ha : (fun θ : Fin n → Bool => f (fun i => θ (S.orderEmbOfFin rfl i))) =
      (fun θ : Fin n → Bool => f (a (fun i => θ i.val))) := by
    rfl
  calc
    _ = mean (fun θ : S → Bool => f (a θ)) := by
      exact (mean_instance_congr _ _ _ _ ha).trans
        ((mean_sign_restrict_subtype S (fun θ => f (a θ))).trans
          (mean_instance_congr _ _ _ _ rfl))
    _ = _ := mean_reindex a f

end SurveyStatements.P5OperatorReduction
