import SurveyStatements.P1SupportStabilizationFusion
import Mathlib.Data.Finset.Preimage
import Mathlib.Analysis.SpecificLimits.Basic

/-! DOSZ Lemma 2.6 in the discrete finite-witness form used by P1: a single
infinite set uniformly makes every finite off-support sum small. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

theorem support_assignment_stabilization_with_budget
    (f : Set ℕ → ℕ → ℂ) (hf : SupportAssignmentLocallyConstant f)
    (hcluster : SupportAssignmentSequentialC0Cluster f)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (ε : ℝ)
    (hbudget : ∀ I : Finset ℕ, ∑ n ∈ I, δ n ≤ ε)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ N : Set ℕ, N ⊆ M ∧ N.Infinite ∧
      ∀ P : Set ℕ, P ⊆ N → P.Infinite →
        ∀ S : Finset ℕ, (S : Set ℕ) ⊆ N \ P → ∑ i ∈ S, ‖f P i‖ ≤ ε := by
  classical
  obtain ⟨ν, T, hν, hνM, _, _, htail, hgood⟩ :=
    support_exists_deletion_fusion f hf hcluster δ hδ M hM
  refine ⟨range ν, ?_, support_infinite_strictMono_range ν hν, ?_⟩
  · rintro x ⟨n, rfl⟩
    exact hνM n
  · intro P hPN hP S hS
    let I : Finset ℕ := S.preimage ν hν.injective.injOn
    have himage : I.image ν = S := by
      rw [Finset.image_preimage]
      apply Finset.filter_eq_self.mpr
      intro i hi
      exact (hS hi).1
    have hsum : ∑ i ∈ S, ‖f P i‖ = ∑ n ∈ I, ‖f P (ν n)‖ := by
      rw [← himage, Finset.sum_image]
      intro a _ b _ hab
      exact hν.injective hab
    rw [hsum]
    apply le_trans (Finset.sum_le_sum ?_) (hbudget I)
    intro n hn
    have hnS : ν n ∈ S := Finset.mem_preimage.mp hn
    exact (support_deletion_fusion_coordinate_bound f δ ν hν T htail hgood
      P hP hPN n (hS hnS).2).le

theorem support_assignment_stabilization
    (f : Set ℕ → ℕ → ℂ) (hf : SupportAssignmentLocallyConstant f)
    (hcluster : SupportAssignmentSequentialC0Cluster f)
    (ε : ℝ) (hε : 0 < ε) (M : Set ℕ) (hM : M.Infinite) :
    ∃ N : Set ℕ, N ⊆ M ∧ N.Infinite ∧
      ∀ P : Set ℕ, P ⊆ N → P.Infinite →
        ∀ S : Finset ℕ, (S : Set ℕ) ⊆ N \ P → ∑ i ∈ S, ‖f P i‖ ≤ ε := by
  let δ : ℕ → ℝ := fun n => (ε / 2) * (1 / 2 : ℝ) ^ n
  have hδ : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  have hrange (K : ℕ) : ∑ n ∈ Finset.range K, δ n ≤ ε := by
    dsimp only [δ]
    rw [← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le K)
      (show 0 ≤ ε / 2 by positivity)
    convert h using 1 <;> ring
  have hbudget (I : Finset ℕ) : ∑ n ∈ I, δ n ≤ ε := by
    have hsub : I ⊆ Finset.range (I.sup id + 1) := by
      intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => (hδ n).le)).trans (hrange _)
  exact support_assignment_stabilization_with_budget f hf hcluster δ hδ ε hbudget M hM

end SurveyStatements.P1
