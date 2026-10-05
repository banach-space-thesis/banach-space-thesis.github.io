import Posets.MainTransfiniteChoice
import Posets.Matrices
import Mathlib.Analysis.Real.Cardinality

/-! Cardinal bookkeeping for Section 5, for either real or complex scalars. -/

noncomputable section
namespace Posets
open Cardinal

theorem rclike_card (𝕜 : Type) [RCLike 𝕜] : #𝕜 = 𝔠 := by
  apply le_antisymm
  · have hi : Function.Injective (fun z : 𝕜 => (RCLike.re z, RCLike.im z)) := by
      intro z w h
      exact RCLike.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
    simpa [Cardinal.mk_real] using Cardinal.mk_le_of_injective hi
  · simpa [Cardinal.mk_real] using Cardinal.mk_le_of_injective (RCLike.ofReal_injective (K := 𝕜))

theorem scalarMatrix_card (𝕜 : Type) [RCLike 𝕜] : #(ScalarMatrix 𝕜) = 𝔠 := by
  simp [ScalarMatrix, rclike_card]

theorem option_repeat_card {σ : Type} (hσ : #σ ≤ 𝔠) : #(Option σ × Set ℕ) = 𝔠 := by
  apply le_antisymm
  · rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_set_nat,
      Cardinal.mk_option]
    calc
      (#σ + 1) * 𝔠 ≤ (𝔠 + 1) * 𝔠 := mul_le_mul_right' (add_le_add_right hσ 1) _
      _ = 𝔠 := by
        rw [Cardinal.add_eq_left Cardinal.aleph0_le_continuum
          (Cardinal.one_le_aleph0.trans Cardinal.aleph0_le_continuum),
          Cardinal.continuum_mul_self]
  · have hi : Function.Injective (fun A : Set ℕ => ((none : Option σ), A)) :=
      fun A B h => congrArg Prod.snd h
    simpa only [Cardinal.mk_set_nat] using Cardinal.mk_le_of_injective hi

theorem continuumStage_card : #ContinuumStage = 𝔠 := by
  simp [ContinuumStage, Cardinal.mk_toType]

def continuumStageEquiv {σ : Type} (hσ : #σ ≤ 𝔠) : ContinuumStage ≃ Option σ × Set ℕ :=
  Classical.choice (Cardinal.eq.mp (continuumStage_card.trans (option_repeat_card hσ).symm))

def setNatPairEquiv : (Set ℕ × Set ℕ) ≃ Set ℕ :=
  Classical.choice (Cardinal.eq.mp (by simp [Cardinal.mk_prod]))

end Posets
