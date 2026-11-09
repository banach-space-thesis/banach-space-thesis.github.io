import PEMS.ALDeBlasiEquality
import PEMS.ContinuousMapDualPositiveWitness
import ThesisCommon.Analysis.PositiveDualFragmentOpenWitness
import ThesisCommon.Analysis.ContinuousMapModulusMeasure
import ThesisCommon.Analysis.ContinuousMapCZeroBlocks
import ThesisCommon.Analysis.CZeroDualEllOne
import ThesisCommon.Analysis.EllOneWeakEssentialIdentity
import ThesisCommon.Analysis.BanachAdjointNorm

/-! The uniform-regularity formula of Lemma 6.2 for arbitrary operators on
the real and complex measure spaces of a compact Hausdorff space. -/

noncomputable section
set_option maxSynthPendingDepth 3
open Set Filter Topology MeasureTheory ThesisCommon
open scoped Function ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice

namespace PEMS

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

section Measures

variable [MeasurableSpace K]

private def uniformRegularityValues {F : Type*} (variation : F → Measure K)
    (A : Set F) : Set ℝ :=
  {r | ∃ U : ℕ → Set K, (∀ n, IsOpen (U n)) ∧ Pairwise (Disjoint on U) ∧
    ∃ φ : ℕ → F, (∀ n, φ n ∈ A) ∧ r = ⨅ n, (variation (φ n)).real (U n)}

/-- The supremum of the infimal variation masses on pairwise disjoint open
sets, using one measure from the bounded set for each open set. -/
def continuousMapUniformRegularity {F : Type*} (variation : F → Measure K)
    (A : Set F) : ℝ := sSup (uniformRegularityValues variation A)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

omit [CompactSpace K] in
private theorem zero_mem_uniformRegularityValues
    (variation : StrongDual 𝕜 C(K, 𝕜) → Measure K)
    (T : E →L[𝕜] StrongDual 𝕜 C(K, 𝕜)) :
    0 ∈ uniformRegularityValues variation (T '' Metric.closedBall 0 1) := by
  refine ⟨fun _ => ∅, fun _ => isOpen_empty, ?_, fun _ => T 0, ?_, ?_⟩
  · intro i j hij
    simp [Function.onFun]
  · intro n
    exact ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩
  · simp

private theorem uniformRegularityValues_bddAbove
    (variation : StrongDual 𝕜 C(K, 𝕜) → Measure K)
    (hmass : ∀ φ U, (variation φ).real U ≤ ‖φ‖)
    (T : E →L[𝕜] StrongDual 𝕜 C(K, 𝕜)) :
    BddAbove (uniformRegularityValues variation (T '' Metric.closedBall 0 1)) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨U, hU, hd, φ, hφ, rfl⟩
  obtain ⟨x, hx, hTx⟩ := hφ 0
  have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  calc
    (⨅ n, (variation (φ n)).real (U n)) ≤ (variation (φ 0)).real (U 0) :=
      ciInf_le ⟨0, by rintro _ ⟨n, rfl⟩; exact ENNReal.toReal_nonneg⟩ 0
    _ ≤ ‖φ 0‖ := hmass _ _
    _ = ‖T x‖ := congrArg norm hTx.symm
    _ ≤ ‖T‖ := (T.le_opNorm x).trans
      ((mul_le_mul_of_nonneg_left hx' (norm_nonneg T)).trans_eq (mul_one _))

private theorem uniformRegularity_le_weakEssentialNorm
    (variation : StrongDual 𝕜 C(K, 𝕜) → Measure K)
    (htest : ∀ φ U r, IsOpen U → r < (variation φ).real U →
      ∃ f : C(K, 𝕜), ‖f‖ ≤ 1 ∧ (∀ t ∉ U, f t = 0) ∧ r < ‖φ f‖)
    (T : E →L[𝕜] StrongDual 𝕜 C(K, 𝕜)) :
    continuousMapUniformRegularity variation (T '' Metric.closedBall 0 1) ≤
      weakEssentialNorm (𝕜 := 𝕜) (E := E) (F := StrongDual 𝕜 C(K, 𝕜)) T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro _ ⟨W, hW, rfl⟩
    apply csSup_le ⟨0, zero_mem_uniformRegularityValues variation T⟩
    rintro _ ⟨U, hU, hUd, φ, hφ, rfl⟩
    apply le_of_not_gt
    intro hlarge
    obtain ⟨c, hcW, hc⟩ := exists_between hlarge
    have hm (n : ℕ) : c < (variation (φ n)).real (U n) :=
      hc.trans_le (ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact ENNReal.toReal_nonneg⟩ n)
    choose f hf hs hval using fun n => htest (φ n) (U n) c (hU n) (hm n)
    let G (n : ℕ) := (ContinuousLinearMap.id 𝕜 𝕜).smulRight (f n)
    have hG (n : ℕ) : ‖G n‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro a
      change ‖a • f n‖ ≤ 1 * ‖a‖
      rw [norm_smul, one_mul]
      exact (mul_le_mul_of_nonneg_left (hf n) (norm_nonneg a)).trans_eq (mul_one _)
    have hdis (i j : ℕ) (hij : i ≠ j) (a b : 𝕜) (t : K) :
        G i a t = 0 ∨ G j b t = 0 := by
      change a * f i t = 0 ∨ b * f j t = 0
      by_cases ht : t ∈ U i
      · exact Or.inr (by rw [hs j t (fun ht' => Set.disjoint_left.mp (hUd hij) ht ht'), mul_zero])
      · exact Or.inl (by rw [hs i t ht, mul_zero])
    let V := continuousMapCZeroInsert G hG hdis
    have hV (n : ℕ) : V (cZeroSingle n (1 : 𝕜)) = f n := by
      rw [show V = continuousMapCZeroInsert G hG hdis from rfl, continuousMapCZeroInsert_single]
      simp [G]
    let Q := (cZeroDualToEllOne (𝕜 := 𝕜)).comp (banachAdjoint V)
    have hQW : IsWeaklyCompactOperator (Q.comp W) := hW.comp_left Q
    obtain ⟨n, hn⟩ := (hQW.scalarEllOne_coordinates_uniformly_small (sub_pos.mpr hcW)).exists
    obtain ⟨x, hx, hTx⟩ := hφ n
    have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hsmall : ‖(W x) (f n)‖ < c - ‖T - W‖ := by
      simpa only [Q, ContinuousLinearMap.comp_apply, cZeroDualToEllOne_apply,
        banachAdjoint_apply, hV] using hn x hx'
    have hdiff : ‖(T x) (f n) - (W x) (f n)‖ ≤ ‖T - W‖ := by
      calc
        ‖(T x) (f n) - (W x) (f n)‖ = ‖((T - W) x) (f n)‖ := by
          simp only [ContinuousLinearMap.sub_apply]
        _ ≤ ‖(T - W) x‖ * ‖f n‖ := ((T - W) x).le_opNorm (f n)
        _ ≤ ‖(T - W) x‖ :=
          (mul_le_mul_of_nonneg_left (hf n) (norm_nonneg _)).trans_eq (mul_one _)
        _ ≤ ‖T - W‖ := ((T - W).le_opNorm x).trans
          ((mul_le_mul_of_nonneg_left hx' (norm_nonneg _)).trans_eq (mul_one _))
    have hbig := hval n
    rw [← hTx] at hbig
    linarith [norm_le_norm_sub_add ((T x) (f n)) ((W x) (f n))]

private theorem weakEssentialNorm_le_uniformRegularity_of_witnesses
    (variation : StrongDual 𝕜 C(K, 𝕜) → Measure K)
    (hmass : ∀ φ U, (variation φ).real U ≤ ‖φ‖)
    (T : E →L[𝕜] StrongDual 𝕜 C(K, 𝕜))
    (hwit : ∀ c, 0 < c → c < weakEssentialNorm (𝕜 := 𝕜) (E := E) (F := StrongDual 𝕜 C(K, 𝕜)) T →
      ∃ (x : ℕ → E) (U : ℕ → Set K), (∀ n, ‖x n‖ = 1) ∧ (∀ n, IsOpen (U n)) ∧
        Pairwise (Disjoint on U) ∧ ∀ n, c < (variation (T (x n))).real (U n)) :
    weakEssentialNorm (𝕜 := 𝕜) (E := E) (F := StrongDual 𝕜 C(K, 𝕜)) T ≤
      continuousMapUniformRegularity variation (T '' Metric.closedBall 0 1) := by
  have hbdd := uniformRegularityValues_bddAbove variation hmass T
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  by_cases hc0 : 0 < c
  · obtain ⟨x, U, hx, hU, hd, hm⟩ := hwit c hc0 hc
    apply (le_ciInf (fun n => (hm n).le)).trans
    apply le_csSup hbdd
    refine ⟨U, hU, hd, fun n => T (x n), ?_, rfl⟩
    intro n
    exact ⟨x n, by simp only [Metric.mem_closedBall, dist_zero_right, hx, le_refl], rfl⟩
  · exact (le_of_not_gt hc0).trans (le_csSup hbdd (zero_mem_uniformRegularityValues variation T))

variable [T2Space K] [BorelSpace K]

private theorem exists_open_mass_of_positive_fragments
    (variation : StrongDual 𝕜 C(K, 𝕜) → Measure K)
    (modulus : StrongDual 𝕜 C(K, 𝕜) → StrongDual ℝ C(K, ℝ))
    (hpos : ∀ φ, 0 ≤ modulus φ) (hnorm : ∀ φ, ‖modulus φ‖ = ‖φ‖)
    (hvariation : ∀ φ, variation φ = positiveContinuousMapRiesz (modulus φ) (hpos φ))
    (T : E →L[𝕜] StrongDual 𝕜 C(K, 𝕜))
    (x : ℕ → E) (ψ : ℕ → StrongDual ℝ C(K, ℝ)) (l : ℝ)
    (hx : ∀ n, ‖x n‖ = 1) (hψ : ∀ n, 0 ≤ ψ n) (hle : ∀ n, ψ n ≤ modulus (T (x n)))
    (hd : Pairwise fun i j => ψ i ⊓ ψ j = 0)
    (hl : weakEssentialNorm (𝕜 := 𝕜) (E := E) (F := StrongDual 𝕜 C(K, 𝕜)) T ≤ l)
    (ht : Tendsto (fun n => ‖ψ n‖) atTop (𝓝 l))
    {c : ℝ} (hc : c < weakEssentialNorm (𝕜 := 𝕜) (E := E) (F := StrongDual 𝕜 C(K, 𝕜)) T) :
    ∃ (x' : ℕ → E) (U : ℕ → Set K), (∀ n, ‖x' n‖ = 1) ∧ (∀ n, IsOpen (U n)) ∧
      Pairwise (Disjoint on U) ∧ ∀ n, c < (variation (T (x' n))).real (U n) := by
  obtain ⟨b, hcb, hbw⟩ := exists_between hc
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (lt_mem_nhds (hbw.trans_le hl)))
  let φ (n : ℕ) := modulus (T (x (N + n)))
  have hφnorm (n : ℕ) : ‖φ n‖ ≤ ‖T‖ := by
    dsimp only [φ]
    rw [hnorm]
    simpa only [hx, mul_one] using T.le_opNorm (x (N + n))
  obtain ⟨k, _, U, hU, hUd, hm⟩ := exists_disjoint_open_of_positive_dual_fragments
    φ (fun n => ψ (N + n)) (fun n => hpos _) (fun n => hψ (N + n)) (fun n => hle (N + n))
    (fun i j hij => hd (fun h => hij (Nat.add_left_cancel h))) hφnorm
    (c := b) (ε := b - c) (fun n => hN (N + n) (Nat.le_add_right N n)) (sub_pos.mpr hcb)
  refine ⟨fun n => x (N + k n), U, fun n => hx _, hU, hUd, ?_⟩
  intro n
  rw [hvariation]
  simpa only [φ, sub_sub_cancel] using hm n

end Measures

variable [T2Space K]

set_option maxHeartbeats 800000 in
/-- Lemma 6.2 over the real field. Here `continuousMapRealModulusMeasure`
is the variation measure of an actual element of `C(K, ℝ)⁎`. -/
theorem lemma_6_2_real (T : StrongDual ℝ C(K, ℝ) →L[ℝ] StrongDual ℝ C(K, ℝ)) :
    letI : MeasurableSpace K := borel K
    letI : BorelSpace K := ⟨rfl⟩
    let ω := deBlasiOperator (𝕜 := ℝ) (E := StrongDual ℝ C(K, ℝ)) (F := StrongDual ℝ C(K, ℝ)) T
    continuousMapUniformRegularity continuousMapRealModulusMeasure (T '' Metric.closedBall 0 1) =
      ω ∧ ω = weakEssentialNorm (𝕜 := ℝ) (E := StrongDual ℝ C(K, ℝ)) (F := StrongDual ℝ C(K, ℝ)) T := by
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  have hω := deBlasiOperator_eq_weakEssentialNorm_real_AL T
    continuousMap_real_dual_isALSpace continuousMap_real_dual_isALSpace
  refine ⟨?_, hω⟩
  rw [hω]
  apply le_antisymm
  · exact uniformRegularity_le_weakEssentialNorm continuousMapRealModulusMeasure
      (fun φ _ _ hU hr => exists_continuousMap_real_open_modulus_test φ hU hr) T
  · refine weakEssentialNorm_le_uniformRegularity_of_witnesses continuousMapRealModulusMeasure ?_ T ?_
    · intro φ U
      rw [← continuousMapRealModulusMeasure_mass φ]
      exact measureReal_mono (subset_univ U)
    · intro c hc0 hc
      have hT : ¬IsWeaklyCompactOperator (𝕜 := ℝ) (E := StrongDual ℝ C(K, ℝ))
          (F := StrongDual ℝ C(K, ℝ)) T := by
        intro h
        rw [h.weakEssentialNorm_eq_zero] at hc
        exact (not_lt_of_ge hc0.le) hc
      obtain ⟨x, ψ, l, hx, hψ, hle, hd, hl, ht⟩ :=
        exists_real_continuousMapDual_disjoint_positiveWitness T hT
      obtain ⟨b, hcb, hbw⟩ := exists_between hc
      obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (lt_mem_nhds (hbw.trans_le hl)))
      let φ (n : ℕ) := dualModulus (T (x (N + n)))
      have hφ (n : ℕ) : 0 ≤ φ n := dualModulus_nonneg _
      have hφnorm (n : ℕ) : ‖φ n‖ ≤ ‖T‖ := by
        dsimp only [φ]
        rw [norm_dualModulus]
        simpa only [hx, mul_one] using T.le_opNorm (x (N + n))
      obtain ⟨k, _, U, hU, hUd, hm⟩ := exists_disjoint_open_of_positive_dual_fragments
        φ (fun n => ψ (N + n)) hφ (fun n => hψ (N + n))
        (fun n => by simpa only [dual_abs_eq_modulus] using hle (N + n))
        (fun i j hij => hd (fun h => hij (Nat.add_left_cancel h))) hφnorm
        (c := b) (ε := b - c) (fun n => hN (N + n) (Nat.le_add_right N n)) (sub_pos.mpr hcb)
      refine ⟨fun n => x (N + k n), U, fun n => hx _, hU, hUd, ?_⟩
      intro n
      have h := hm n
      change b - (b - c) < (continuousMapRealModulusMeasure
        (T (x (N + k n)))).real (U n) at h
      simpa only [sub_sub_cancel] using h

/-- Lemma 6.2 over the complex field, using total variation rather than
the absolute value of the measure of the open set. -/
theorem lemma_6_2_complex (T : StrongDual ℂ C(K, ℂ) →L[ℂ] StrongDual ℂ C(K, ℂ)) :
    letI : MeasurableSpace K := borel K
    letI : BorelSpace K := ⟨rfl⟩
    let ω := deBlasiOperator (𝕜 := ℂ) (E := StrongDual ℂ C(K, ℂ)) (F := StrongDual ℂ C(K, ℂ)) T
    continuousMapUniformRegularity continuousMapComplexModulusMeasure (T '' Metric.closedBall 0 1) =
      ω ∧ ω = weakEssentialNorm (𝕜 := ℂ) (E := StrongDual ℂ C(K, ℂ)) (F := StrongDual ℂ C(K, ℂ)) T := by
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  have hω := deBlasiOperator_eq_weakEssentialNorm_complex_AL T
    continuousMap_complex_dual_isALSpace continuousMap_complex_dual_isALSpace
  refine ⟨?_, hω⟩
  rw [hω]
  apply le_antisymm
  · exact uniformRegularity_le_weakEssentialNorm continuousMapComplexModulusMeasure
      (fun φ _ _ hU hr => exists_continuousMap_complex_open_modulus_test φ hU hr) T
  · refine weakEssentialNorm_le_uniformRegularity_of_witnesses continuousMapComplexModulusMeasure ?_ T ?_
    · intro φ U
      rw [← continuousMapComplexModulusMeasure_mass φ]
      exact measureReal_mono (subset_univ U)
    · intro c hc0 hc
      have hT : ¬IsWeaklyCompactOperator (𝕜 := ℂ) (E := StrongDual ℂ C(K, ℂ))
          (F := StrongDual ℂ C(K, ℂ)) T := by
        intro h
        rw [h.weakEssentialNorm_eq_zero] at hc
        exact (not_lt_of_ge hc0.le) hc
      obtain ⟨x, ψ, l, hx, hψ, hle, hd, hl, ht⟩ :=
        exists_complex_continuousMapDual_disjoint_positiveWitness T hT
      exact exists_open_mass_of_positive_fragments continuousMapComplexModulusMeasure
        continuousMapComplexModulus continuousMapComplexModulus_nonneg norm_continuousMapComplexModulus
        (fun _ => rfl) T x ψ l hx hψ hle hd hl ht hc

end PEMS
