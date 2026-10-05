import ThesisCommon.Analysis.GowersMaureyCodedPairSelection

/-! The genuine special functional detects the operator on the sum of the
constructed pairs. The off-diagonal error is explicitly summed; the operator
still acts on its original subspace. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
variable {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ} {seed k : ℕ} {G : C00 𝕜 → ℝ}

theorem CodedDetectingFamily.row_detection (d : CodedDetectingFamily T ε η seed k G)
    (hη : 0 ≤ η) (hbudget : (k : ℝ)*η ≤ ε/32) (i : Fin k) :
    ε/32 ≤ ∑ j, RCLike.re (completedPairing D (d.pair i).functional (T (d.pair j).inSubspace)) := by
  classical
  let b (j : Fin k) := completedPairing D (d.pair i).functional (T (d.pair j).inSubspace)
  have ho : ∀ j, j ≠ i → ‖b j‖ ≤ η := by
    intro j hji
    rcases lt_or_gt_of_ne hji with h | h
    · exact (d.cross_image j i h).2.le
    · exact (d.cross_image i j h).1.le
  have hnorm : ‖∑ j ∈ Finset.univ.erase i, b j‖ ≤ (k : ℝ)*η := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖b j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase i, η :=
        Finset.sum_le_sum (fun j hj => ho j (Finset.ne_of_mem_erase hj))
      _ ≤ ∑ _j : Fin k, η := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun _ _ _ => hη)
      _ = _ := by simp
  have hre := RCLike.re_le_norm (-(∑ j ∈ Finset.univ.erase i, b j))
  rw [map_neg,norm_neg] at hre
  have hdiag : ε/16 < RCLike.re (b i) := (d.pair i).detected
  have hsum := Finset.sum_erase_add Finset.univ b (Finset.mem_univ i)
  have hs : (∑ j, RCLike.re (b j)) = RCLike.re (∑ j ∈ Finset.univ.erase i, b j) +
      RCLike.re (b i) := by rw [← map_sum,← hsum,map_add]
  change ε/32 ≤ ∑ j, RCLike.re (b j)
  rw [hs]
  linarith

theorem CodedDetectingFamily.special_sum_detection
    (d : CodedDetectingFamily T ε η seed k G) (hη : 0 ≤ η)
    (hbudget : (k : ℝ)*η ≤ ε/32) :
    (k : ℝ)*ε/(32*Real.sqrt (logarithmicWeight k)) ≤
      RCLike.re (completedPairing D (specialFunctional (fun i => (d.pair i).functional))
        (T (∑ i, (d.pair i).inSubspace))) := by
  have hsm (r : ℝ) (a : C00 𝕜) : r • a = (r : 𝕜) • a := by
    ext n
    simp only [Finsupp.smul_apply,smul_eq_mul,RCLike.real_smul_eq_coe_mul]
  rw [specialFunctional,hsm,map_smul,map_sum]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,smul_eq_mul,
    RCLike.re_ofReal_mul,map_sum]
  have hs : (k : ℝ)*(ε/32) ≤
      ∑ i, ∑ j, RCLike.re (completedPairing D (d.pair i).functional (T (d.pair j).inSubspace)) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => d.row_detection hη hbudget i)
  calc
    _ = (Real.sqrt (logarithmicWeight k))⁻¹ * ((k : ℝ)*(ε/32)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

theorem CodedDetectingFamily.operator_sum_lower_bound
    (d : CodedDetectingFamily T ε η (k-1) k G) (hk : k ∈ D.specialSizes)
    (hη : 0 ≤ η) (hbudget : (k : ℝ)*η ≤ ε/32) :
    (k : ℝ)*ε/(32*Real.sqrt (logarithmicWeight k)) ≤
      ‖T (∑ i, (d.pair i).inSubspace)‖ := by
  have hu := (d.specialSequence (D.specialSize_pos hk)).specialFunctional_dualUnit D hk
  exact (d.special_sum_detection hη hbudget).trans
    ((RCLike.re_le_norm _).trans (completedPairing_norm_bound hu _))

end ThesisCommon.GowersMaurey
