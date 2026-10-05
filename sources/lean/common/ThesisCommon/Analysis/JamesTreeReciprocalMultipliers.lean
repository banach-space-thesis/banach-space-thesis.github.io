import ThesisCommon.Analysis.JamesTreeMultipliers
import ThesisCommon.Analysis.DyadicScalarOscillationSelection
import ThesisCommon.Analysis.JamesTreeAntichainNorms

/-! Uniform reciprocal operators derived from the actual selected scalar
coefficients. The only inputs are lower and finite-chain oscillation bounds;
the bounded operators and their full-vector inverse identity are conclusions. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem exists_jamesTree_reciprocal_multipliers (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (hchain : JamesTreeSegmentsAreChains S) (d : DyadicTreeNode → 𝕜)
    {a M ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε)
    (hlower : ∀ t, a ≤ ‖d t‖) (hM : ∀ t, ‖d t‖ ≤ M)
    (hdev : ∀ A, IsLiteralTreeSegment A → ∃ t ∈ A, (∑ s ∈ A, ‖d s-d t‖) ≤ ε) :
    ∃ D B : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S,
      (∀ x t, jamesTreeCoordinate t (D x) = d t * jamesTreeCoordinate t x) ∧
      (∀ x t, jamesTreeCoordinate t (B x) = (d t)⁻¹ * jamesTreeCoordinate t x) ∧
      B.comp D = ContinuousLinearMap.id 𝕜 _ ∧
      ‖D‖ ≤ M+ε ∧ ‖B‖ ≤ a⁻¹ + ε/(a*a) := by
  have hM0 : 0 ≤ M := (norm_nonneg (d [])).trans (hM [])
  have hC : 0 ≤ M+ε := add_nonneg hM0 hε
  have hK : 0 ≤ a⁻¹ + ε/(a*a) := by positivity
  have hd : JamesTreeCoefficientBound S d (M+ε) := by
    intro A hA
    obtain ⟨t, _, ht⟩ := hdev A (hchain A hA)
    exact ⟨d t, add_le_add (hM t) ht⟩
  have hi : JamesTreeCoefficientBound S (fun t => (d t)⁻¹) (a⁻¹ + ε/(a*a)) :=
    fun A hA => dyadic_chain_reciprocal_bound d ha hlower hdev (hchain A hA)
  refine ⟨jamesTreeMultiplier hp hS d hC hd,
    jamesTreeMultiplier hp hS (fun t => (d t)⁻¹) hK hi,
    fun x t => jamesTreeCoordinate_multiplier hp hS d hC hd t x,
    fun x t => jamesTreeCoordinate_multiplier hp hS (fun t => (d t)⁻¹) hK hi t x,
    jamesTreeMultiplier_reciprocal_comp hp hS d
      (fun t => norm_pos_iff.mp (ha.trans_le (hlower t))) hC hK hd hi,
    norm_jamesTreeMultiplier_le hp hS d hC hd,
    norm_jamesTreeMultiplier_le hp hS (fun t => (d t)⁻¹) hK hi⟩

theorem exists_jamesTree_selected_reciprocal_multipliers (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (hchain : JamesTreeSegmentsAreChains S) (f : DyadicTreeNode → 𝕜)
    (e g : DyadicSubtreeEmbedding) {a M : ℝ} (ha : 0 < a)
    (hlower : ∀ t, a ≤ ‖f (e t)‖) (hM : ∀ t, ‖f t‖ ≤ M)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hanti : Antitone δ) (hsum : Summable δ)
    (hosc : ∀ s t, s.IsPrefix t → ‖f (e s)-f (e t)‖ ≤ δ s.length) :
    ∃ D B : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S,
      (∀ x t, jamesTreeCoordinate t (D x) = f ((e.comp g) t) * jamesTreeCoordinate t x) ∧
      (∀ x t, jamesTreeCoordinate t (B x) = (f ((e.comp g) t))⁻¹ * jamesTreeCoordinate t x) ∧
      B.comp D = ContinuousLinearMap.id 𝕜 _ ∧
      ‖D‖ ≤ M+(∑' n, δ n) ∧ ‖B‖ ≤ a⁻¹ + (∑' n, δ n)/(a*a) := by
  apply exists_jamesTree_reciprocal_multipliers hp hS hchain (fun t => f ((e.comp g) t)) ha
    (tsum_nonneg hδ) (fun t => hlower (g t)) (fun t => hM _)
  apply dyadic_chain_scalar_oscillation _ δ hδ hsum
  have h := dyadic_descendant_oscillation_comp f e g δ hanti
    (fun s t hst => by simpa only [dist_eq_norm] using hosc s t hst)
  simpa only [dist_eq_norm] using h

end ThesisCommon
