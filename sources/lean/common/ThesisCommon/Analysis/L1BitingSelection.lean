import ThesisCommon.Analysis.BoundedTailProfiles
import ThesisCommon.Analysis.L1UniformTailCriterion
import Mathlib.Analysis.SpecificLimits.Basic

/-! The constructive biting selection for bounded scalar L1 sequences.
Coordinatewise limits of tail masses determine the escaping mass. Removing
rapidly growing high-level sets leaves a uniformly integrable subsequence. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
  [IsFiniteMeasure μ]

theorem exists_lOne_uniformIntegrable_tail_complements
    (f : ℕ → Lp 𝕜 1 μ) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C)
    (L : ℕ → ℕ) (hL : ∀ k, k ≤ L k) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      UniformIntegrable (fun k =>
        (lpCut (lOneTailSet (f (r k)) (L k))ᶜ
          (measurableSet_lOneTailSet (f (r k)) (L k)).compl (f (r k)) : X → 𝕜)) 1 μ := by
  let b : ℕ → ℕ → ℝ := fun n m => lOneTailMass (f n) m
  have hb : ∀ n m, 0 ≤ b n m ∧ b n m ≤ C := fun n m =>
    ⟨(lOneTailMass_bounds _ _).1, (lOneTailMass_bounds _ _).2.trans (hf n)⟩
  obtain ⟨a, α, r₀, hr₀, ha, hanti, hαa, hα, hta, htb⟩ :=
    exists_antitone_profile_limit b hb (fun n => lOneTailMass_antitone (f n))
  let η : ℕ → ℝ := fun k => (2⁻¹ : ℝ) ^ k
  have hη : ∀ k, 0 < η k := fun k => pow_pos (by norm_num) k
  have htη : Tendsto η atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨s, hs, hsall, hsL⟩ := exists_profile_diagonal_choice
    (fun n m => b (r₀ n) m) a htb L η hη
  refine ⟨r₀ ∘ s, hr₀.comp hs, ?_⟩
  apply uniformIntegrable_of_eventually_lOneTailMass
  intro ε hε
  obtain ⟨M, hM⟩ := (hta.eventually (gt_mem_nhds (by linarith : α < α + ε / 3))).exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (htη.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3)))
  refine ⟨M, max M N, fun k hk => ?_⟩
  have hMk : M ≤ k := (le_max_left _ _).trans hk
  have hNk : N ≤ k := (le_max_right _ _).trans hk
  rw [lOneTailMass_cut_compl _ (hMk.trans (hL k))]
  have heM := (abs_lt.mp (hsall k M hMk)).2
  have heL := (abs_lt.mp (hsL k)).1
  have hae := hαa (L k)
  have he := hN k hNk
  change b (r₀ (s k)) M - b (r₀ (s k)) (L k) ≤ ε
  linarith

theorem exists_lOne_biting_subsequence
    (f : ℕ → Lp 𝕜 1 μ) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ A : ℕ → Set X,
      ∃ hA : ∀ k, MeasurableSet (A k),
      (∑' k, μ (A k)) ≠ ∞ ∧
      UniformIntegrable (fun k => (lpCut (A k)ᶜ (hA k).compl (f (r k)) : X → 𝕜)) 1 μ := by
  have hchoose (k : ℕ) : ∃ l : ℕ, k ≤ l ∧ C / ((l : ℝ) + 1) ≤ (2⁻¹ : ℝ) ^ k := by
    have hp : 0 < (2⁻¹ : ℝ) ^ k := pow_pos (by norm_num) _
    obtain ⟨m, hm⟩ := exists_nat_gt (C / (2⁻¹ : ℝ) ^ k)
    refine ⟨max k m, le_max_left _ _, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < ((max k m : ℕ) : ℝ) + 1)).mpr
    have hcm : C < (m : ℝ) * (2⁻¹ : ℝ) ^ k := (div_lt_iff₀ hp).mp hm
    have hml : (m : ℝ) ≤ (max k m : ℕ) := Nat.cast_le.mpr (le_max_right _ _)
    nlinarith
  choose L hL hsmall using hchoose
  obtain ⟨r, hr, hUI⟩ := exists_lOne_uniformIntegrable_tail_complements f hf L hL
  refine ⟨r, hr, fun k => lOneTailSet (f (r k)) (L k),
    fun k => measurableSet_lOneTailSet _ _, ?_, hUI⟩
  apply ne_top_of_le_ne_top (b := ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k)
  · simp
  · apply ENNReal.tsum_le_tsum
    intro k
    apply (measure_lOneTailSet_le _ _).trans
    have hle : ‖f (r k)‖ / ((L k : ℝ) + 1) ≤ (2⁻¹ : ℝ) ^ k :=
      (div_le_div_of_nonneg_right (hf _) (by positivity)).trans (hsmall k)
    convert ENNReal.ofReal_le_ofReal hle using 1 <;>
      simp [ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos, inv_pow, ENNReal.inv_pow]

end ThesisCommon
