import Posets.Models
import PosetsCommon.CZeroSumFinite

/-! Diagonal operators on a dependent c₀ sum, for the product construction in §7. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open Filter Topology ThesisCommon
open scoped ENNReal
namespace Posets

variable {𝕜 : Type} [RCLike 𝕜] {P : Type*}
  {X C : P → Type*}
  [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, NormedAddCommGroup (C p)] [∀ p, NormedSpace 𝕜 (C p)]

theorem product_sumInjection_norm (p : P) (x : X p) :
    ‖sumInjection 𝕜 X p x‖ = ‖x‖ := by
  classical
  change ‖lp.single ∞ p x‖ = ‖x‖
  exact lp.norm_single (by simp) p x

theorem product_operatorBlock_norm_le
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (s t : P) :
    ‖operatorBlock 𝕜 X X T s t‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  exact (sumProjection_norm_le (T (sumInjection 𝕜 X t x)) s).trans
    (by simpa only [product_sumInjection_norm] using T.le_opNorm (sumInjection 𝕜 X t x))

variable (ρ : ∀ p, C p →L[𝕜] (X p →L[𝕜] X p))
  (hρ : ∀ p a, ‖ρ p a‖ ≤ ‖a‖)

include hρ

theorem productSection_coord_bound (a : lp C ∞) (x : DependentCZeroSum 𝕜 X) (p : P) :
    ‖ρ p (a p) (x.val p)‖ ≤ ‖a‖ * ‖x.val p‖ :=
  ((ρ p (a p)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
    ((hρ p _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero a p)) (norm_nonneg _))

theorem productSection_uniform_bound (a : lp C ∞) (x : DependentCZeroSum 𝕜 X) (p : P) :
    ‖ρ p (a p) (x.val p)‖ ≤ ‖a‖ * ‖x‖ :=
  (productSection_coord_bound ρ hρ a x p).trans (mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm ENNReal.top_ne_zero x.val p) (norm_nonneg a))

/-- Apply each coordinate section to the matching c₀ coordinate. -/
def productSectionValue (a : lp C ∞) :
    DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X :=
  ({ toFun := fun x =>
      ⟨⟨fun p => ρ p (a p) (x.val p), memℓp_infty
        ⟨‖a‖ * ‖x‖, by rintro _ ⟨p, rfl⟩; exact productSection_uniform_bound ρ hρ a x p⟩⟩,
        by
          apply squeeze_zero (fun p => norm_nonneg _) (productSection_coord_bound ρ hρ a x)
          simpa using x.property.const_mul ‖a‖⟩
     map_add' := by
       intro x y
       apply Subtype.ext
       apply lp.ext
       funext p
       exact map_add (ρ p (a p)) (x.val p) (y.val p)
     map_smul' := by
       intro r x
       apply Subtype.ext
       apply lp.ext
       funext p
       exact map_smul (ρ p (a p)) r (x.val p) } :
    DependentCZeroSum 𝕜 X →ₗ[𝕜] DependentCZeroSum 𝕜 X).mkContinuous ‖a‖
    (fun x => lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg a) (norm_nonneg x))
      (productSection_uniform_bound ρ hρ a x))

theorem productSectionValue_apply (a : lp C ∞) (x : DependentCZeroSum 𝕜 X) (p : P) :
    (productSectionValue ρ hρ a x).val p = ρ p (a p) (x.val p) := rfl

theorem productSectionValue_norm_le (a : lp C ∞) :
    ‖productSectionValue ρ hρ a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro x
  exact lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg a) (norm_nonneg x))
    (productSection_uniform_bound ρ hρ a x)

/-- Linearity of the diagonal section on the uniformly bounded product. -/
def productSectionLinearMap : lp C ∞ →ₗ[𝕜]
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :=
  { toFun := productSectionValue ρ hρ
    map_add' := by
       intro a b
       apply ContinuousLinearMap.ext
       intro x
       apply Subtype.ext
       apply lp.ext
       funext p
       change ρ p (a p + b p) (x.val p) = _
       rw [map_add]
       rfl
    map_smul' := by
       intro r a
       apply ContinuousLinearMap.ext
       intro x
       apply Subtype.ext
       apply lp.ext
       funext p
       change ρ p (r • a p) (x.val p) = _
       rw [map_smul]
       rfl }

/-- The bounded linear diagonal section on the uniformly bounded product. -/
def productSectionMap : lp C ∞ →L[𝕜]
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) := by
  refine LinearMap.mkContinuous (productSectionLinearMap ρ hρ) 1 ?_
  intro a
  change ‖productSectionValue ρ hρ a‖ ≤ 1 * ‖a‖
  simpa only [one_mul] using productSectionValue_norm_le ρ hρ a

theorem productSectionMap_apply (a : lp C ∞) (x : DependentCZeroSum 𝕜 X) (p : P) :
    (productSectionMap ρ hρ a x).val p = ρ p (a p) (x.val p) := rfl

theorem productSectionMap_diagonal (a : lp C ∞) (p : P) :
    operatorBlock 𝕜 X X (productSectionMap ρ hρ a) p p = ρ p (a p) := by
  apply ContinuousLinearMap.ext
  intro x
  change ρ p (a p) ((sumInjection 𝕜 X p x).val p) = _
  simp [sumInjection]

theorem productSectionMap_offDiagonal (a : lp C ∞) (s t : P) (hst : s ≠ t) :
    operatorBlock 𝕜 X X (productSectionMap ρ hρ a) s t = 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  change ρ s (a s) ((sumInjection 𝕜 X t x).val s) = 0
  simp [sumInjection, Pi.single_eq_of_ne hst]

end Posets
