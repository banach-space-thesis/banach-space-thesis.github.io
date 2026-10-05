import Posets.WolfeLaminarEmbeddingFactorization
import Posets.WolfeLaminarEmbeddingRankTop

/-! Actual identity factors supported on one compact clopen top cell.
The ambient space need not be compact: all quotient functions are extended
by zero from the top cell before the given operator is applied. -/

noncomputable section
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
variable {K ι X : Type*} [TopologicalSpace K] [T2Space K]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace X]

theorem wolfeClopenTop_factorization
    (H : Set K) [CompactSpace H] [Countable H] (hH : IsClopen H)
    (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) (hcA : ∀ i, IsCompact (A i))
    (hAH : ∀ i, A i ⊆ H) (hunit : ∃ i, A i = H)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ (s : Finset ι) (a : ι → 𝕜),
      c * ‖∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)‖ ≤
        ‖T (∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i))‖)
    {α : Ordinal.{0}} (hα : α ≠ 0) (hcα : α.card ≤ Cardinal.aleph0)
    (hD : (ordinalDerived (univ : Set (WolfeClopenTopQuotient H A hA)) α).Nonempty) :
    ∃ I : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] JLMS.CZero 𝕜 K,
    ∃ R : X →L[𝕜] OrdinalContinuous 𝕜 (ω ^ α),
      R.comp (T.comp I) = ContinuousLinearMap.id 𝕜 _ ∧ ‖I‖ ≤ 1 ∧ ‖R‖ ≤ 1 / c := by
  obtain ⟨V⟩ := exists_ordinal_isometry_of_derivative_nonempty (𝕜 := 𝕜)
    (WolfeClopenTopQuotient H A hA) hα hD
  let J := (wolfeClopenTopIsometry (𝕜 := 𝕜) H hH A hA).comp V
  have hJ : ∀ f, c * ‖f‖ ≤ ‖(T.comp J.toContinuousLinearMap) f‖ := by
    intro f
    have h := wolfeClopenTopIsometry_lower_bound H hH A hA hcA hAH hunit hlam T c hbound (V f)
    simpa only [LinearIsometry.norm_map] using h
  obtain ⟨S, R, hR, hS, hnR⟩ := exists_countable_ordinal_embedding_identity_factors hcα
    (T.comp J.toContinuousLinearMap) hc hJ
  refine ⟨J.toContinuousLinearMap.comp S, R, ?_, ?_, hnR⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using hR
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖J (S f)‖ ≤ 1 * ‖f‖
    rw [J.norm_map, one_mul]
    exact (S.le_opNorm f).trans (by simpa using mul_le_mul_of_nonneg_right hS (norm_nonneg f))

/-- A ranked family whose surviving cells occur among the coordinates gives
the required quotient rank, and hence actual ordinal identity factors. -/
theorem rankedWolfeFamily_clopenTop_factorization {P : Type*}
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{0}) (B Leaves : Set P)
    (H : Set K) [CompactSpace H] [Countable H] (hH : IsClopen H)
    (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) (hcA : ∀ i, IsCompact (A i))
    (hAH : ∀ i, A i ⊆ H) (hunit : ∃ i, A i = H)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ (s : Finset ι) (a : ι → 𝕜),
      c * ‖∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)‖ ≤
        ‖T (∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i))‖)
    (β : Ordinal.{0})
    (hcell : ∀ p ∈ B, (v p).2.Nonempty ∧ IsCompact (v p).2)
    (hcoord : ∀ δ p, p ∈ rankedWolfeFamily v height B Leaves δ →
      β ≤ δ → (v p).2 ⊆ H → ∃ i, A i = (v p).2)
    {α : Ordinal.{0}} (hα : α ≠ 0) (hcα : α.card ≤ Cardinal.aleph0) {p : P}
    (hp : p ∈ rankedWolfeFamily v height B Leaves (β + α)) (hpH : (v p).2 ⊆ H) :
    ∃ I : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] JLMS.CZero 𝕜 K,
    ∃ R : X →L[𝕜] OrdinalContinuous 𝕜 (ω ^ α),
      R.comp (T.comp I) = ContinuousLinearMap.id 𝕜 _ ∧ ‖I‖ ≤ 1 ∧ ‖R‖ ≤ 1 / c := by
  apply wolfeClopenTop_factorization H hH A hA hcA hAH hunit hlam T hc hbound hα hcα
  exact (rankedWolfeFamily_clopenTop_ordinalDerived v height B Leaves H A hA β
    hcell hcoord α hp hpH).mono inter_subset_right

end Posets
