import NonCalkinAlgebra.EigenvectorFlags
import NonCalkinAlgebra.CompactSpectral
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open Module Topology Filter Set
universe v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Compactness rules out infinitely many distinct eigenvalues bounded away
from zero. This is the Riesz finite-flag argument on an arbitrary Banach space;
no orthogonality, normality, or self-adjointness assumption is used. -/
theorem compact_eigenvector_sequence_impossible (T : X →L[ℂ] X)
    (hT : IsCompactOperator T) (μ : ℕ → ℂ) (hμinj : Function.Injective μ)
    (ε : ℝ) (hε : 0 < ε) (hμnorm : ∀ n, ε ≤ ‖μ n‖)
    (v : ℕ → X) (heigen : ∀ n, Module.End.HasEigenvector (T : End ℂ X) (μ n) (v n)) :
    False := by
  classical
  have hμpos (n : ℕ) : 0 < ‖μ n‖ := hε.trans_le (hμnorm n)
  have hμne (n : ℕ) : μ n ≠ 0 := norm_pos_iff.mp (hμpos n)
  have hv := Module.End.eigenvectors_linearIndependent' (T : End ℂ X) μ hμinj v heigen
  have hveq (n : ℕ) : T (v n) = μ n • v n := (heigen n).apply_eq_smul
  obtain ⟨f, hfmem, hfnorm, hffar⟩ := eigenvectorFlag_separated_sequence v hv
  let g (n : ℕ) : X := (μ n)⁻¹ • T (f n)
  have hgdiff (n : ℕ) : g n - f n ∈ eigenvectorSpan v n := by
    have hd := eigenvectorSpan_defect_lowers T μ v hveq n (hfmem n)
    have heq : g n - f n = (μ n)⁻¹ • (T (f n) - μ n • f n) := by
      rw [smul_sub, inv_smul_smul₀ (hμne n)]
    rw [heq]
    exact (eigenvectorSpan v n).smul_mem _ hd
  have hgmem {m n : ℕ} (hmn : m < n) : g m ∈ eigenvectorSpan v n := by
    apply eigenvectorSpan_mono v (Nat.succ_le_of_lt hmn)
    exact (eigenvectorSpan v (m + 1)).smul_mem _
      (operator_preserves_eigenvectorSpan T μ v hveq (m + 1) (hfmem m))
  have hlt (m n : ℕ) (hmn : m < n) : 1 ≤ ‖g n - g m‖ := by
    have hy : g m - (g n - f n) ∈ eigenvectorSpan v n :=
      (eigenvectorSpan v n).sub_mem (hgmem hmn) (hgdiff n)
    have heq : f n - (g m - (g n - f n)) = g n - g m := by abel
    simpa only [heq] using hffar n _ hy
  have hpair : Pairwise (fun m n => 1 ≤ ‖g m - g n‖) := by
    intro m n hne
    rcases lt_or_gt_of_ne hne with hmn | hnm
    · simpa only [norm_sub_rev] using hlt m n hmn
    · exact hlt n m hnm
  obtain ⟨K, hK, hKmem⟩ := hT.image_closedBall_subset_compact 3
  let C : Set ℂ := Metric.closedBall 0 ε⁻¹
  let L : Set X := (fun p : ℂ × X => p.1 • p.2) '' (C ×ˢ K)
  have hL : IsCompact L := (isCompact_closedBall (0 : ℂ) ε⁻¹).prod hK |>.image
    (continuous_fst.smul continuous_snd)
  have hgL (n : ℕ) : g n ∈ L := by
    refine ⟨((μ n)⁻¹, T (f n)), ⟨?_, ?_⟩, rfl⟩
    · change (μ n)⁻¹ ∈ Metric.closedBall (0 : ℂ) ε⁻¹
      rw [Metric.mem_closedBall, dist_zero_right, norm_inv]
      exact (inv_le_inv₀ (hμpos n) hε).mpr (hμnorm n)
    · apply hKmem
      exact ⟨f n, by simpa only [Metric.mem_closedBall, dist_zero_right] using hfnorm n, rfl⟩
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := hL.tendsto_subseq hgL
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq 1 zero_lt_one
  have hsmall : ‖g (ψ (N + 1)) - g (ψ N)‖ < 1 := by
    simpa only [dist_eq_norm_sub] using hN (N + 1) (Nat.le_succ N)
  exact hsmall.not_ge (hpair (hψ.injective.ne (Nat.succ_ne_self N)))

theorem compact_eigenvalues_finite_outside (T : X →L[ℂ] X)
    (hT : IsCompactOperator T) (ε : ℝ) (hε : 0 < ε) :
    {z : ℂ | Module.End.HasEigenvalue (T : End ℂ X) z ∧ ε ≤ ‖z‖}.Finite := by
  classical
  by_contra hfinite
  let S := {z : ℂ | Module.End.HasEigenvalue (T : End ℂ X) z ∧ ε ≤ ‖z‖}
  have hS : S.Infinite := hfinite
  let e : ℕ ↪ S := hS.natEmbedding S
  let μ (n : ℕ) : ℂ := (e n).val
  have hμinj : Function.Injective μ := by
    intro m n hmn
    exact e.injective (Subtype.ext hmn)
  have heigen (n : ℕ) : Module.End.HasEigenvalue (T : End ℂ X) (μ n) := (e n).property.1
  have hμnorm (n : ℕ) : ε ≤ ‖μ n‖ := (e n).property.2
  choose v hv using (fun n => (heigen n).exists_hasEigenvector)
  exact compact_eigenvector_sequence_impossible T hT μ hμinj ε hε hμnorm v hv

variable [CompleteSpace X]

theorem compact_spectrum_finite_outside (T : X →L[ℂ] X)
    (hT : IsCompactOperator T) (ε : ℝ) (hε : 0 < ε) :
    {z : ℂ | z ∈ spectrum ℂ T ∧ ε ≤ ‖z‖}.Finite := by
  apply (compact_eigenvalues_finite_outside T hT ε hε).subset
  intro z hz
  have hzne : z ≠ 0 := norm_pos_iff.mp (hε.trans_le hz.2)
  exact ⟨(CompactSpectral.hasEigenvalue_iff_mem_spectrum hT hzne).mpr hz.1, hz.2⟩

/-- The compact spectrum is countable, on arbitrary complex Banach spaces. -/
theorem compact_spectrum_countable (T : X →L[ℂ] X) (hT : IsCompactOperator T) :
    (spectrum ℂ T).Countable := by
  have hc : ({0} ∪ ⋃ n : ℕ, {z : ℂ | z ∈ spectrum ℂ T ∧
      1 / (n + 1 : ℝ) ≤ ‖z‖}).Countable :=
    (Set.finite_singleton (0 : ℂ)).countable.union
      (Set.countable_iUnion (fun n =>
        (compact_spectrum_finite_outside T hT (1 / (n + 1 : ℝ)) (by positivity)).countable))
  apply hc.mono
  intro z hz
  by_cases hz0 : z = 0
  · exact Or.inl (Set.mem_singleton_iff.mpr hz0)
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hz0)
    exact Or.inr (Set.mem_iUnion.mpr ⟨n, hz, hn.le⟩)

end NonCalkinAlgebra
