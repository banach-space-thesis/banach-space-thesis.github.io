import ThesisCommon.Analysis.SchauderMatrix
import ThesisCommon.Analysis.FiniteHistory
import Mathlib.Order.Interval.Finset.Nat

/-! The two-sided gliding-hump step in Theorem 3.3. The earlier indices and
the length of the finite history fix the next tolerance before the next
index is chosen. Thus ordinary row and column convergence suffice.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon

/-- Simultaneously make both directions of a matrix small along a strictly
increasing subsequence of any prescribed infinite set. -/
theorem two_sided_matrix_selection (w : ℕ → ℕ → ℝ)
    (hrow : ∀ m, Tendsto (w m) atTop (𝓝 0))
    (hcol : ∀ m, Tendsto (fun n => w n m) atTop (𝓝 0))
    {M : Set ℕ} (hM : M.Infinite) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (∀ n, f n ∈ M) ∧
      ∀ i j, i < j → w (f i) (f j) < ε / (2 : ℝ) ^ (i + j + 2) ∧
        w (f j) (f i) < ε / (2 : ℝ) ^ (i + j + 2) := by
  classical
  let P : ℕ → Finset ℕ → Prop := fun n F => ∀ m ∈ F,
    w m n < ε / (2 : ℝ) ^ (m + F.card + 2) ∧
    w n m < ε / (2 : ℝ) ^ (m + F.card + 2)
  have hnext : ∀ F : Finset ℕ, (∀ m ∈ F, m ∈ M) →
      ∃ n ∈ M, (∀ m ∈ F, m < n) ∧ P n F := by
    intro F _
    have hev : ∀ᶠ n in atTop, ∀ m ∈ F, m < n ∧
        w m n < ε / (2 : ℝ) ^ (m + F.card + 2) ∧
        w n m < ε / (2 : ℝ) ^ (m + F.card + 2) := by
      apply (Filter.eventually_all_finset F).mpr
      intro m _
      have hp : 0 < ε / (2 : ℝ) ^ (m + F.card + 2) := by positivity
      exact (eventually_gt_atTop m).and
        (((hrow m).eventually (gt_mem_nhds hp)).and
          ((hcol m).eventually (gt_mem_nhds hp)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    obtain ⟨n, hn, hNn⟩ := hM.exists_gt N
    exact ⟨n, hn, fun m hm => (hN n hNn.le m hm).1,
      fun m hm => (hN n hNn.le m hm).2⟩
  obtain ⟨f, hf, hmem, hP⟩ := increasing_finite_history M P hnext
  refine ⟨f, hf, hmem, ?_⟩
  intro i j hij
  have hh := hP j (f i) (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij, rfl⟩)
  have hcard : ((Finset.range j).image f).card = j := by
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_range]
  change w (f i) (f j) < ε / (2 : ℝ) ^ (f i + ((Finset.range j).image f).card + 2) ∧
    w (f j) (f i) < ε / (2 : ℝ) ^ (f i + ((Finset.range j).image f).card + 2) at hh
  rw [hcard] at hh
  have hbound : ε / (2 : ℝ) ^ (f i + j + 2) ≤ ε / (2 : ℝ) ^ (i + j + 2) := by
    apply div_le_div_of_nonneg_left hε.le (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    have hi : i ≤ f i := hf.id_le i
    omega
  exact ⟨hh.1.trans_le hbound, hh.2.trans_le hbound⟩

namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Apply the preceding recursion to a bounded operator. Column convergence
is proved from the Schauder expansion; the weak-null input is still explicit. -/
theorem small_off_diagonal_subsequence (b : NormalizedSchauderBasis 𝕜 X)
    (hweak : ∀ f : X →L[𝕜] 𝕜, Tendsto (fun n => f (b.vector n)) atTop (𝓝 0))
    (T : X →L[𝕜] X) {M : Set ℕ} (hM : M.Infinite) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (∀ n, f n ∈ M) ∧
      ∀ i j, i ≠ j → ‖b.coord (f i) (T (b.vector (f j)))‖ <
        ε / (2 : ℝ) ^ (i + j + 2) := by
  obtain ⟨f, hf, hm, hs⟩ := two_sided_matrix_selection
    (fun m n => ‖b.coord m (T (b.vector n))‖)
    (fun m => by simpa using (hweak ((b.coord m).comp T)).norm)
    (fun m => by simpa using (b.coord_tendsto_zero (T (b.vector m))).norm) hM hε
  refine ⟨f, hf, hm, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (hs i j hij).1
  · simpa only [Nat.add_comm j i] using (hs j i hji).2

end NormalizedSchauderBasis
end ThesisCommon
