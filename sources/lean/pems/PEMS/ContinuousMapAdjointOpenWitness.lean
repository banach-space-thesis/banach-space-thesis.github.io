import PEMS.ContinuousMapDualPositiveWitness
import ThesisCommon.Analysis.PositiveDualFragmentOpenWitness
import ThesisCommon.Analysis.ContinuousMapModulusMeasure

/-! Sharp disjoint open witnesses for the weak essential norm of an
actual C(K)-operator adjoint, with no metrizability or sequential
compactness assumption. -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open Set Filter Topology MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice
namespace PEMS
variable {K L : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]
  [MeasurableSpace L] [BorelSpace L]

theorem exists_real_adjoint_disjoint_open_witness
    (T : C(L, ℝ) →L[ℝ] C(K, ℝ)) {c : ℝ} (hc0 : 0 < c)
    (hc : c < dualWeakEssentialNorm T) :
    ∃ (ν : ℕ → StrongDual ℝ C(K, ℝ)) (U : ℕ → Set L),
      (∀ n, ‖ν n‖ = 1) ∧ (∀ n, IsOpen (U n)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ∀ n, c < (continuousMapRealModulusMeasure (banachAdjoint T (ν n))).real (U n) := by
  have hT : ¬IsWeaklyCompactOperator (banachAdjoint T) := by
    intro h
    have hz := IsWeaklyCompactOperator.weakEssentialNorm_eq_zero (𝕜 := ℝ)
      (E := StrongDual ℝ C(K, ℝ)) (F := StrongDual ℝ C(L, ℝ)) h
    change c < weakEssentialNorm (banachAdjoint T) at hc
    rw [hz] at hc
    linarith
  obtain ⟨x, ψ, l, hx, hψ, hle, hd, hl, ht⟩ :=
    exists_real_continuousMapDual_disjoint_positiveWitness (banachAdjoint T) hT
  obtain ⟨b, hcb, hbw⟩ := exists_between hc
  have hbl : b < l := hbw.trans_le hl
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (lt_mem_nhds hbl))
  let φ (n : ℕ) := dualModulus (banachAdjoint T (x (N + n)))
  have hφ (n : ℕ) : 0 ≤ φ n := dualModulus_nonneg _
  have hφnorm (n : ℕ) : ‖φ n‖ ≤ ‖banachAdjoint T‖ := by
    dsimp only [φ]
    rw [norm_dualModulus]
    simpa only [hx, mul_one] using (banachAdjoint T).le_opNorm (x (N + n))
  obtain ⟨k, _, U, hU, hUd, hm⟩ := exists_disjoint_open_of_positive_dual_fragments
    φ (fun n => ψ (N + n)) hφ (fun n => hψ (N + n))
    (fun n => by simpa only [dual_abs_eq_modulus] using hle (N + n))
    (fun i j hij => hd (fun h => hij (Nat.add_left_cancel h))) hφnorm
    (c := b) (ε := b - c) (fun n => hN (N + n) (Nat.le_add_right N n)) (sub_pos.mpr hcb)
  refine ⟨fun n => x (N + k n), U, fun n => hx _, hU, hUd, ?_⟩
  intro n
  have h := hm n
  change b - (b - c) < (continuousMapRealModulusMeasure
    (banachAdjoint T (x (N + k n)))).real (U n) at h
  simpa only [sub_sub_cancel] using h

theorem exists_complex_adjoint_disjoint_open_witness
    (T : C(L, ℂ) →L[ℂ] C(K, ℂ)) {c : ℝ} (hc0 : 0 < c)
    (hc : c < dualWeakEssentialNorm T) :
    ∃ (ν : ℕ → StrongDual ℂ C(K, ℂ)) (U : ℕ → Set L),
      (∀ n, ‖ν n‖ = 1) ∧ (∀ n, IsOpen (U n)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ∀ n, c < (continuousMapComplexModulusMeasure (banachAdjoint T (ν n))).real (U n) := by
  have hT : ¬IsWeaklyCompactOperator (banachAdjoint T) := by
    intro h
    have hz := IsWeaklyCompactOperator.weakEssentialNorm_eq_zero (𝕜 := ℂ)
      (E := StrongDual ℂ C(K, ℂ)) (F := StrongDual ℂ C(L, ℂ)) h
    change c < weakEssentialNorm (banachAdjoint T) at hc
    rw [hz] at hc
    linarith
  obtain ⟨x, ψ, l, hx, hψ, hle, hd, hl, ht⟩ :=
    exists_complex_continuousMapDual_disjoint_positiveWitness (banachAdjoint T) hT
  obtain ⟨b, hcb, hbw⟩ := exists_between hc
  have hbl : b < l := hbw.trans_le hl
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (lt_mem_nhds hbl))
  let φ (n : ℕ) := continuousMapComplexModulus (banachAdjoint T (x (N + n)))
  have hφ (n : ℕ) : 0 ≤ φ n := continuousMapComplexModulus_nonneg _
  have hφnorm (n : ℕ) : ‖φ n‖ ≤ ‖banachAdjoint T‖ := by
    dsimp only [φ]
    rw [norm_continuousMapComplexModulus]
    simpa only [hx, mul_one] using (banachAdjoint T).le_opNorm (x (N + n))
  obtain ⟨k, _, U, hU, hUd, hm⟩ := exists_disjoint_open_of_positive_dual_fragments
    φ (fun n => ψ (N + n)) hφ (fun n => hψ (N + n)) (fun n => hle (N + n))
    (fun i j hij => hd (fun h => hij (Nat.add_left_cancel h))) hφnorm
    (c := b) (ε := b - c) (fun n => hN (N + n) (Nat.le_add_right N n)) (sub_pos.mpr hcb)
  refine ⟨fun n => x (N + k n), U, fun n => hx _, hU, hUd, ?_⟩
  intro n
  have h := hm n
  change b - (b - c) < (continuousMapComplexModulusMeasure
    (banachAdjoint T (x (N + k n)))).real (U n) at h
  simpa only [sub_sub_cancel] using h

end PEMS
