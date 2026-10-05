import Posets.ManyMaximalIdealsEvaluation
import Mathlib.Analysis.Real.Cardinality

/-! Exact cardinality, rather than only a lower bound, for the maximal
closed ideals of scalar ℓ∞ over either scalar field. -/
noncomputable section
open Cardinal ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem rclike_cardinal_le_continuum : #𝕜 ≤ 𝔠 := by
  have hinj : Function.Injective (fun z : 𝕜 => (RCLike.re z, RCLike.im z)) := by
    intro z w h
    exact RCLike.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  simpa only [mk_prod, mk_real, lift_id, continuum_mul_self] using mk_le_of_injective hinj

theorem scalarBoundedProduct_cardinal_le_continuum : #(ScalarBoundedProduct 𝕜) ≤ 𝔠 := by
  have hcoe : #(ScalarBoundedProduct 𝕜) ≤ #(ℕ → 𝕜) :=
    mk_le_of_injective (fun _ _ h => lp.ext h)
  have hfun : #(ℕ → 𝕜) ≤ 𝔠 := by
    rw [mk_arrow, lift_id, lift_id, mk_nat]
    exact (power_le_power_right (rclike_cardinal_le_continuum (𝕜 := 𝕜))).trans_eq
      continuum_power_aleph0
  exact hcoe.trans hfun

theorem scalarBoundedProductMaximalIdeals_cardinal_le :
    #(MaximalClosedIdeals 𝕜 (ScalarBoundedProduct 𝕜)) ≤ #(Set (Set ℕ)) := by
  calc
    _ ≤ #(Set (ScalarBoundedProduct 𝕜)) := mk_subtype_le _
    _ ≤ #(Set (Set ℕ)) := by
      rw [mk_set, mk_set, mk_set_nat]
      exact power_le_power_left (by norm_num)
        (scalarBoundedProduct_cardinal_le_continuum (𝕜 := 𝕜))

theorem scalarBoundedProductMaximalIdeals_cardinal :
    #(MaximalClosedIdeals 𝕜 (ScalarBoundedProduct 𝕜)) = #(Set (Set ℕ)) :=
  le_antisymm scalarBoundedProductMaximalIdeals_cardinal_le
    (manyScalarMaximalIdealsEmbedding (𝕜 := 𝕜)).cardinal_le

/-- The literal set-of-sets cardinal appearing in Corollary 8.6. -/
def scalarBoundedProductMaximalIdealsEquiv :
    MaximalClosedIdeals 𝕜 (ScalarBoundedProduct 𝕜) ≃ Set (Set ℕ) :=
  Classical.choice (Cardinal.eq.mp scalarBoundedProductMaximalIdeals_cardinal)

end Posets
