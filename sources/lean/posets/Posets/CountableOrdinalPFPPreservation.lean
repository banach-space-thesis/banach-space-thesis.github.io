import Posets.CountableOrdinalPFPCrossBands
import Posets.CountableOrdinalPFPAmbient
import Posets.OrdinalCofinalBlockEmbedding
import Posets.OrdinalLiftRetraction
import JLMS.Rudin

/-! The canonical ordinal tower, finite-band pruning and cross-block
selection give an actual preserved ordinal copy. The proved continuous-lift
retraction then turns preservation into identity factorisation. -/

noncomputable section
open Set Topology TopologicalSpace Order ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {θ γ : Ordinal.{0}}
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem ordinalTower_identity_factorization
    (hcθ : θ.card ≤ Cardinal.aleph0) (hcγ : γ.card ≤ Cardinal.aleph0)
    (hγ : IsSuccLimit γ) (hθ : θ ∈ ordinalTowerLevel θ γ)
    (hmul : ∀ β < γ, ∀ N : ℕ, β * N < γ)
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _) :
    ∃ (b : Bool) (I : OrdinalContinuous 𝕜 (ω ^ γ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
      (R : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] OrdinalContinuous 𝕜 (ω ^ γ)),
      R.comp ((if b then T else S).comp I) = ContinuousLinearMap.id 𝕜 _ := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (ordinalIic_compact θ)
  letI : Countable (Iic θ) := ordinalIic_countable_of_card hcθ
  letI : SeparableSpace (JLMS.CZero 𝕜 (Iic θ)) := ordinalIicCZero_separable hcθ
  let M : JLMS.AtomicDualModel 𝕜 (Iic θ) :=
    (JLMS.exists_atomicDualModel (JLMS.scattered_subtype JLMS.scattered_ordinal _)).some
  obtain ⟨b, β, hβ, hcof, lower, F, hgap, hd, hcross⟩ :=
    ordinalTower_exists_cofinal_cross_bands hcθ hcγ hγ hθ hmul M T S hTS
      (by norm_num : (0 : ℝ) < 1 / 32)
  let U := if b then T else S
  letI : ∀ n, CompactSpace (F n).top.cell := fun n =>
    isCompact_iff_compactSpace.mp (F n).top.cell_isCompact
  let Q (n : ℕ) : Type _ := (F n).Quotient
  obtain ⟨J, _, hJ⟩ := exists_ordinalCofinalBlockEmbedding_boundedBelow (𝕜 := 𝕜)
    γ hγ hcγ Q (fun n => (β n).val) hβ.monotone hcof (fun n => (F n).quotient_rank _ (hgap n))
  let E := ordinalTowerBandsIsometry F hd
  let A := E.toContinuousLinearMap.comp J
  let c := (9 / 32 : ℝ) * ordinalCofinalBlockLowerBound (𝕜 := 𝕜) γ hγ hcγ
  have hc : 0 < c := mul_pos (by norm_num) (ordinalCofinalBlockLowerBound_pos γ hγ hcγ)
  have hlower (f : OrdinalContinuous 𝕜 (ω ^ γ)) : c * ‖f‖ ≤ ‖(U.comp A) f‖ := by
    have h := ordinalTowerBands_lower_bound F hθ hd (by norm_num : (0 : ℝ) ≤ 1 / 32)
      (fun n => by rw [hgap n]; exact Ordinal.le_add_right _ _)
      (fun n q hq => (hcross n q hq).le) (J f)
    have h1 : (9 / 32 : ℝ) * ‖J f‖ ≤ ‖U (A f)‖ := by
      norm_num only [show (1 / 2 : ℝ) - 7 * (1 / 32) = 9 / 32 by norm_num] at h
      exact h
    calc
      c * ‖f‖ = (9 / 32 : ℝ) *
          (ordinalCofinalBlockLowerBound (𝕜 := 𝕜) γ hγ hcγ * ‖f‖) := by dsimp [c]; ring
      _ ≤ (9 / 32 : ℝ) * ‖J f‖ := mul_le_mul_of_nonneg_left (hJ f) (by norm_num)
      _ ≤ ‖(U.comp A) f‖ := h1
  obtain ⟨V, R, hR, _, _⟩ := exists_ordinal_embedding_identity_factors hγ.ne_bot hcγ
    (U.comp A) hc hlower
  refine ⟨b, A.comp V, R, ?_⟩
  simpa only [ContinuousLinearMap.comp_assoc] using hR

end Posets
