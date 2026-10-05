import ThesisCommon.Analysis.GowersMaureySpecialHighMatrix
import ThesisCommon.Analysis.GowersMaureySpecialLowCodeBounds
import ThesisCommon.Analysis.GowersMaureySuccessiveIntervalCuts
import ThesisCommon.Analysis.GowersMaureyIntervalSpreadBounds

/-! Bounds on the high-code part of a competing special functional, first
on full blocks and then on genuine interval cuts. The boundary cost is
derived from the actual two partially cut blocks. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
variable {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ} {G : C00 𝕜 → ℝ}

theorem specialHighFunctional_eq_sum {k : ℕ} (D : ConstructionData 𝕜)
    (g : Fin k → C00 𝕜) (t : ℕ) :
    specialHighFunctional D g t = (Real.sqrt (logarithmicWeight k))⁻¹ •
      ∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j), g j := by
  classical
  have hs : (∑ j ∈ Finset.univ.filter (fun j => specialSequenceSize D g j ≤ D.j (2*t)), g j) +
      (∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j), g j) = ∑ j, g j := by
    simpa only [not_le] using Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => specialSequenceSize D g j ≤ D.j (2*t)) g
  rw [specialHighFunctional,specialFunctional,specialLowFunctional,← smul_sub,← hs,add_sub_cancel_left]

theorem CodedDetectingFamily.high_full_blocks_bound {t : ℕ}
    (d : CodedDetectingFamily T ε η (D.j (2*t)-1) (D.j (2*t)) G)
    {g : Fin (D.j (2*t)) → C00 𝕜} (hg : SpecialSequence D (implicitNorm D) g)
    (s : Finset (Fin (D.j (2*t)))) (m n : ℕ) :
    ‖pairing (specialHighFunctional D g t) (spread m n (∑ i ∈ s, (d.pair i).vector))‖ ≤ ‖T‖+14 := by
  classical
  rw [specialHighFunctional_eq_sum,pairing_real_smul_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  simp only [pairing_sum_left,map_sum]
  have hs : ‖∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j),
      ∑ i ∈ s, pairing (g j) (spread m n (d.pair i).vector)‖ ≤ ‖T‖+14 := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j),
          ‖∑ i ∈ s, pairing (g j) (spread m n (d.pair i).vector)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j),
          ∑ i ∈ s, ‖pairing (g j) (spread m n (d.pair i).vector)‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
      _ = ∑ i ∈ s, ∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j),
          ‖pairing (g j) (spread m n (d.pair i).vector)‖ := Finset.sum_comm
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => D.j (2*t) < specialSequenceSize D g j),
          ‖pairing (g j) (spread m n (d.pair i).vector)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => by positivity)
      _ ≤ _ := d.high_interaction_sum_le hg m n
  have hweight : 1 ≤ Real.sqrt (logarithmicWeight (D.j (2*t))) :=
    Real.one_le_sqrt.mpr (one_le_logarithmicWeight (D.j_positive _))
  have hinv : (Real.sqrt (logarithmicWeight (D.j (2*t))))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hweight
  rw [Finset.sum_comm] at hs
  calc
    _ ≤ (Real.sqrt (logarithmicWeight (D.j (2*t))))⁻¹ * (‖T‖+14) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ 1*(‖T‖+14) := mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = _ := one_mul _

theorem CodedDetectingFamily.high_spread_restrict_bound {t : ℕ}
    (d : CodedDetectingFamily T ε η (D.j (2*t)-1) (D.j (2*t)) G)
    {g : Fin (D.j (2*t)) → C00 𝕜} (hg : SpecialSequence D (implicitNorm D) g)
    (E : Interval) (m n : ℕ) :
    ‖pairing (specialHighFunctional D g t) (spread m n (restrict E (∑ i, (d.pair i).vector)))‖ ≤
      ‖T‖+24 := by
  classical
  let full := ∑ i ∈ intervalFullBlocks (fun i => (d.pair i).vector) E, (d.pair i).vector
  let err := restrict E (∑ i, (d.pair i).vector) - full
  have he : restrict E (∑ i, (d.pair i).vector) = full+err := by dsimp [err]; abel
  have herr : implicitNorm D err ≤ 8 := by
    simpa only [show (2 : ℝ)*4 = 8 by norm_num] using
      d.successive.interval_boundary_norm_le (by norm_num : (0 : ℝ) ≤ 4)
        (fun i => (d.pair i).norm_bound) E
  have hf := d.high_full_blocks_bound hg (intervalFullBlocks (fun i => (d.pair i).vector) E) m n
  have hb := hg.highFunctional_le_five_quarters (denseEmbedding D (spread m n err))
  rw [completedPairing_denseEmbedding,denseEmbedding_norm] at hb
  have hb' : ‖pairing (specialHighFunctional D g t) (spread m n err)‖ ≤ 10 := by
    have hn := (implicitNorm_spread_le D m n err).trans herr
    change _ ≤ (5/4 : ℝ)*implicitNorm D (spread m n err) at hb
    linarith
  rw [he,map_add,map_add]
  exact (norm_add_le _ _).trans (by change _ ≤ ‖T‖+24; linarith)

theorem CodedDetectingFamily.special_affine_exception_bound {t : ℕ}
    (d : CodedDetectingFamily T ε η (D.j (2*t)-1) (D.j (2*t)) G)
    {g : Fin (D.j (2*t)) → C00 𝕜} (hg : SpecialSequence D (implicitNorm D) g)
    (E F : Interval) (m n : ℕ) :
    ‖pairing (specialFunctional g) (restrict E (spread m n (restrict F (∑ i, (d.pair i).vector))))‖ ≤
      ‖T‖+24+(1/4 : ℝ)*implicitNorm D (restrict F (∑ i, (d.pair i).vector)) := by
  have hhi := d.high_spread_restrict_bound hg ((E.spreadImage n m).inter F) m n
  rw [← restrict_restrict,← restrict_spread_pullback] at hhi
  have hlo := hg.lowFunctional_restrict_spread_bound E m n (restrict F (∑ i, (d.pair i).vector))
  let z := restrict E (spread m n (restrict F (∑ i, (d.pair i).vector)))
  have he : pairing (specialFunctional g) z = pairing (specialHighFunctional D g t) z +
      pairing (specialLowFunctional D g t) z := by
    rw [← completedPairing_denseEmbedding D _ z,← completedPairing_denseEmbedding D _ z,
      ← completedPairing_denseEmbedding D _ z,← ContinuousLinearMap.add_apply,← map_add]
    congr 2
    exact (sub_add_cancel _ _).symm
  change ‖pairing (specialFunctional g) z‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hhi hlo)

end ThesisCommon.GowersMaurey
