import ThesisCommon.Analysis.JamesOperatorCharacter

/-! Alternating row and column selection for a double limit. The selected
matrix approximates the summing-basis matrix, with summable product errors.
This is a scalar selection lemma; it assumes no operator factorisation. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
  (z : ℕ → ℕ → 𝕜) (ξ : ℕ → 𝕜) (L : 𝕜) (w : ℕ → ℝ)
  (hz : ∀ n, Tendsto (z n) atTop (𝓝 0))
  (hξ : ∀ k, Tendsto (fun n => z n k) atTop (𝓝 (ξ k)))
  (hL : Tendsto ξ atTop (𝓝 L)) (hw : ∀ n, 0 < w n)

include hz hξ hL hw in
private theorem andrew_array_next_exists (n : ℕ) (f : Fin n → ℕ × ℕ) :
    ∃ a b : ℕ, (∀ i, (f i).1 < a ∧ (f i).2 < b) ∧
      ‖ξ a - L‖ < w n ∧ ‖z b a - ξ a‖ < w n * w n ∧
      (∀ i, ‖z (f i).2 a‖ < w n * w i.val) ∧
      (∀ i, ‖z b (f i).1 - ξ (f i).1‖ < w i.val * w n) := by
  have ha₁ : ∀ᶠ a in atTop, ∀ i : Fin n, (f i).1 < a :=
    eventually_all.mpr (fun i => eventually_gt_atTop _)
  have ha₂ : ∀ᶠ a in atTop, ‖ξ a - L‖ < w n :=
    (tendsto_order.1 (hL.sub_const L).norm).2 _ (by simpa using hw n)
  have ha₃ : ∀ᶠ a in atTop, ∀ i : Fin n, ‖z (f i).2 a‖ < w n * w i.val :=
    eventually_all.mpr (fun i => (tendsto_order.1 (hz (f i).2).norm).2 _
      (by simpa using mul_pos (hw n) (hw i.val)))
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := (ha₁.and (ha₂.and ha₃)).exists
  have hb₁ : ∀ᶠ b in atTop, ∀ i : Fin n, (f i).2 < b :=
    eventually_all.mpr (fun i => eventually_gt_atTop _)
  have hb₂ : ∀ᶠ b in atTop, ‖z b a - ξ a‖ < w n * w n :=
    (tendsto_order.1 ((hξ a).sub_const (ξ a)).norm).2 _
      (by simpa using mul_pos (hw n) (hw n))
  have hb₃ : ∀ᶠ b in atTop, ∀ i : Fin n, ‖z b (f i).1 - ξ (f i).1‖ < w i.val * w n :=
    eventually_all.mpr (fun i => (tendsto_order.1 ((hξ (f i).1).sub_const _).norm).2 _
      (by simpa using mul_pos (hw i.val) (hw n)))
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := (hb₁.and (hb₂.and hb₃)).exists
  exact ⟨a, b, fun i => ⟨ha₁ i, hb₁ i⟩, ha₂, hb₂, ha₃, hb₃⟩

private def andrewArrayNext (n : ℕ) (f : Fin n → ℕ × ℕ) : ℕ × ℕ :=
  let a := (andrew_array_next_exists z ξ L w hz hξ hL hw n f).choose
  (a, (andrew_array_next_exists z ξ L w hz hξ hL hw n f).choose_spec.choose)

private theorem andrewArrayNext_spec (n : ℕ) (f : Fin n → ℕ × ℕ) :
    let ab := andrewArrayNext z ξ L w hz hξ hL hw n f
    (∀ i, (f i).1 < ab.1 ∧ (f i).2 < ab.2) ∧
      ‖ξ ab.1 - L‖ < w n ∧ ‖z ab.2 ab.1 - ξ ab.1‖ < w n * w n ∧
      (∀ i, ‖z (f i).2 ab.1‖ < w n * w i.val) ∧
      (∀ i, ‖z ab.2 (f i).1 - ξ (f i).1‖ < w i.val * w n) :=
  (andrew_array_next_exists z ξ L w hz hξ hL hw n f).choose_spec.choose_spec

private def andrewArraySequence (n : ℕ) : ℕ × ℕ :=
  andrewArrayNext z ξ L w hz hξ hL hw n
    (fun i : Fin n => andrewArraySequence i.val)
termination_by n
decreasing_by exact i.isLt

include hz hξ hL hw in
theorem exists_andrew_array_subsequences :
    ∃ α β : ℕ → ℕ, StrictMono α ∧ StrictMono β ∧
      (∀ i, ‖ξ (α i) - L‖ < w i) ∧
      (∀ i j, ‖z (β j) (α i) - (if i ≤ j then ξ (α i) else 0)‖ < w i * w j) := by
  let g := andrewArraySequence z ξ L w hz hξ hL hw
  have hg (n : ℕ) : (∀ i : Fin n, (g i.val).1 < (g n).1 ∧ (g i.val).2 < (g n).2) ∧
      ‖ξ (g n).1 - L‖ < w n ∧ ‖z (g n).2 (g n).1 - ξ (g n).1‖ < w n * w n ∧
      (∀ i : Fin n, ‖z (g i.val).2 (g n).1‖ < w n * w i.val) ∧
      (∀ i : Fin n, ‖z (g n).2 (g i.val).1 - ξ (g i.val).1‖ < w i.val * w n) := by
    have he : g n = andrewArrayNext z ξ L w hz hξ hL hw n (fun i : Fin n => g i.val) := by
      dsimp only [g]
      rw [andrewArraySequence]
    simpa only [← he] using andrewArrayNext_spec z ξ L w hz hξ hL hw n (fun i : Fin n => g i.val)
  refine ⟨fun n => (g n).1, fun n => (g n).2, ?_, ?_, fun i => (hg i).2.1, ?_⟩
  · intro i j hij
    exact ((hg j).1 ⟨i, hij⟩).1
  · intro i j hij
    exact ((hg j).1 ⟨i, hij⟩).2
  · intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [if_pos hij.le]
      exact (hg j).2.2.2.2 ⟨i, hij⟩
    · rw [if_pos le_rfl]
      exact (hg i).2.2.1
    · rw [if_neg (not_le_of_gt hji), sub_zero]
      exact (hg i).2.2.2.1 ⟨j, hji⟩

end ThesisCommon
