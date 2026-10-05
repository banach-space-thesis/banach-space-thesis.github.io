import ThesisCommon.Analysis.DyadicBranchVariation
import Mathlib.Data.Finset.Max

/-! Finite-chain consequences of descendant oscillation. These estimates
survive arbitrary further strong-subtree selection, so gapped chains do
not require any unproved identification with consecutive branches. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

theorem literalTreeSegment_exists_last {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) : ∃ t ∈ A, ∀ s ∈ A, s.IsPrefix t := by
  obtain ⟨t, ht, hmax⟩ := A.exists_max_image List.length hA.1
  refine ⟨t, ht, ?_⟩
  intro s hs
  rcases hA.2 s hs t ht with h | h
  · exact h
  · have heq := h.eq_of_length ((hmax s hs).antisymm h.length_le).symm
    rw [heq]

theorem literalTreeSegment_length_injOn {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) : Set.InjOn List.length (A : Set DyadicTreeNode) := by
  intro s hs t ht heq
  rcases hA.2 s hs t ht with h | h
  · exact h.eq_of_length heq
  · exact (h.eq_of_length heq.symm).symm

theorem literalTreeSegment_sum_length_le {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hsum : Summable δ) : (∑ t ∈ A, δ t.length) ≤ ∑' n, δ n := by
  classical
  rw [← Finset.sum_image (literalTreeSegment_length_injOn hA)]
  exact hsum.sum_le_tsum _ (fun n _ => hδ n)

theorem DyadicSubtreeEmbedding.length_le (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    s.length ≤ (e s).length := by
  induction s using List.reverseRecOn with
  | nil => exact Nat.zero_le _
  | append_singleton s b ih =>
    have h := (e.split_prefix s b).length_le
    simp only [List.length_append, List.length_singleton] at h ⊢
    omega

theorem dyadic_descendant_oscillation_comp {K : Type*} [PseudoMetricSpace K]
    (f : DyadicTreeNode → K) (e g : DyadicSubtreeEmbedding)
    (δ : ℕ → ℝ) (hδ : Antitone δ)
    (he : ∀ s t, s.IsPrefix t → dist (f (e s)) (f (e t)) ≤ δ s.length) :
    ∀ s t, s.IsPrefix t → dist (f ((e.comp g) s)) (f ((e.comp g) t)) ≤ δ s.length := by
  intro s t hst
  exact (he (g s) (g t) ((g.prefix_iff s t).mpr hst)).trans (hδ (g.length_le s))

variable {𝕜 : Type*} [RCLike 𝕜]

theorem dyadic_chain_scalar_oscillation (d : DyadicTreeNode → 𝕜)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hsum : Summable δ)
    (hd : ∀ s t, s.IsPrefix t → ‖d s-d t‖ ≤ δ s.length)
    {A : Finset DyadicTreeNode} (hA : IsLiteralTreeSegment A) :
    ∃ t ∈ A, (∑ s ∈ A, ‖d s-d t‖) ≤ ∑' n, δ n := by
  obtain ⟨t, ht, hlast⟩ := literalTreeSegment_exists_last hA
  exact ⟨t, ht, (Finset.sum_le_sum fun s hs => hd s t (hlast s hs)).trans
    (literalTreeSegment_sum_length_le hA δ hδ hsum)⟩

theorem dyadic_chain_reciprocal_bound (d : DyadicTreeNode → 𝕜)
    {a ε : ℝ} (ha : 0 < a) (hlower : ∀ t, a ≤ ‖d t‖)
    (hdev : ∀ A, IsLiteralTreeSegment A →
      ∃ t ∈ A, (∑ s ∈ A, ‖d s-d t‖) ≤ ε)
    {A : Finset DyadicTreeNode} (hA : IsLiteralTreeSegment A) :
    ∃ c : 𝕜, ‖c‖ + ∑ t ∈ A, ‖(d t)⁻¹-c‖ ≤ a⁻¹ + ε / (a*a) := by
  obtain ⟨t, ht, hsum⟩ := hdev A hA
  have hne (s) : d s ≠ 0 := norm_pos_iff.mp (ha.trans_le (hlower s))
  have hinv : ‖(d t)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le ha (hlower t)
  have hpoint (s) : ‖(d s)⁻¹-(d t)⁻¹‖ ≤ ‖d s-d t‖ / (a*a) := by
    have heq := dist_inv_inv₀ (hne s) (hne t)
    simp only [dist_eq_norm] at heq
    rw [heq]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos ha ha)
      (mul_le_mul (hlower s) (hlower t) ha.le (norm_nonneg _))
  refine ⟨(d t)⁻¹, add_le_add hinv ?_⟩
  calc
    _ ≤ ∑ s ∈ A, ‖d s-d t‖ / (a*a) := Finset.sum_le_sum fun s _ => hpoint s
    _ = (∑ s ∈ A, ‖d s-d t‖) / (a*a) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ε / (a*a) := div_le_div_of_nonneg_right hsum (mul_nonneg ha.le ha.le)

end ThesisCommon
