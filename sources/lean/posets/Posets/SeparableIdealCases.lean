import Posets.OrdinalIdealTransportOmega
import Posets.ProductIdealMatrix
import ThesisCommon.Analysis.UncountableCompactMetricPrimariness

/-! The finite and uncountable compact metric cases of Corollary 3.3.
The countably infinite case is isolated explicitly for ordinal classification. -/
noncomputable section
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def finiteContinuousMapIsometryEquiv (K : Type) [TopologicalSpace K]
    [T2Space K] [CompactSpace K] [Fintype K] : C(K, 𝕜) ≃ₗᵢ[𝕜] (K → 𝕜) where
  toEquiv := ContinuousMap.equivFnOfDiscrete
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    change ‖(fun x : K => f x)‖ = ‖f‖
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm x)
    · exact (ContinuousMap.norm_le _ (norm_nonneg (fun x : K => f x))).mpr
        (fun x => norm_le_pi_norm (fun y : K => f y) x)

theorem finite_compact_uniqueMaximalClosedIdeal (K : Type) [TopologicalSpace K]
    [T2Space K] [CompactSpace K] [Finite K] [Nonempty K] :
    HasUniqueMaximalClosedIdeal 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜)) := by
  letI : Fintype K := Fintype.ofFinite K
  apply (uniqueMaximalClosed_operator_equiv
    (finiteContinuousMapIsometryEquiv (𝕜 := 𝕜) K).toContinuousLinearEquiv).mpr
  refine ⟨{0}, (fullFiniteOperator_maximalClosedIdeal_iff _).mpr rfl, ?_⟩
  intro I hI
  exact (fullFiniteOperator_maximalClosedIdeal_iff I).mp hI

theorem uncountable_compactMetric_uniqueMaximalClosedIdeal (K : Type)
    [MetricSpace K] [CompactSpace K] [Uncountable K] :
    HasUniqueMaximalClosedIdeal 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜)) :=
  (uniqueMaximal_of_hasPFP (uncountable_compactMetric_hasUPFP (𝕜 := 𝕜) K).hasPFP).2

/-- Only the countably infinite compact metric case is needed after the two
checked branches above. -/
theorem corollary_3_3_of_countablyInfinite
    (hcount : ∀ (K : Type) [MetricSpace K] [CompactSpace K] [Countable K] [Infinite K],
      HasUniqueMaximalClosedIdeal 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜))) : Corollary_3_3 𝕜 := by
  intro K _ _ _
  classical
  cases finite_or_infinite K with
  | inl h =>
    letI := h
    exact finite_compact_uniqueMaximalClosedIdeal K
  | inr h =>
    letI := h
    by_cases hc : Countable K
    · letI := hc
      exact hcount K
    · letI : Uncountable K := ⟨hc⟩
      exact uncountable_compactMetric_uniqueMaximalClosedIdeal K

theorem countable_compact_uniqueMaximalClosedIdeal_of_ordinalModel
    (hord : ∀ α : Ordinal.{0}, Proposition_3_1 𝕜 α)
    (K : Type) [MetricSpace K] [CompactSpace K]
    (hmodel : ∃ α : Ordinal.{0}, Ordinal.omega0 ≤ α ∧
      Nonempty (K ≃ₜ Set.Icc (0 : Ordinal.{0}) α)) :
    HasUniqueMaximalClosedIdeal 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜)) := by
  obtain ⟨α, hα, ⟨e⟩⟩ := hmodel
  exact (uniqueMaximalClosed_operator_equiv (continuousMapHomeomorphEquiv e)).mpr
    ((hord α hα).1)

end Posets
