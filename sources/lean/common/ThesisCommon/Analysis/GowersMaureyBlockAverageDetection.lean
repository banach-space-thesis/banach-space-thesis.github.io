import ThesisCommon.Analysis.GowersMaureyBlockAverageFunctionals
import ThesisCommon.Analysis.GowersMaureyNPairOperatorBounds
import ThesisCommon.Analysis.FiniteWeightedDetection

/-! Error accounting for the common norming functional in Lemma 9.
Every entry is a genuine completed functional evaluation; the bound counts
all off-diagonal entries, including those from different RIS blocks. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem normalizedPairSum_norm_le_of_entry_bounds (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) (a : Fin N → C00 𝕜) (u : Fin N → E)
    (T : E →L[𝕜] ShiftSpace D) {η : ℝ}
    (hentry : ∀ i j, ‖completedPairing D (a i) (T (u j))‖ ≤ η) :
    ‖completedPairing D (averagedPairFunctional a)
      (T (normalizedPairSum (𝕜 := 𝕜) u))‖ ≤ N*η := by
  rw [completedPairing_normalizedPairSum D hN,norm_mul,norm_inv,RCLike.norm_natCast]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ i, ∑ j, η := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hentry i j)))))
      (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = N*η := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp

theorem combined_average_re_lower_bound (D : ConstructionData 𝕜)
    {k N : ℕ} (hN : 0 < N) (a : Fin k → Fin N → C00 𝕜)
    (u : Fin N → E) (T : E →L[𝕜] ShiftSpace D) (i : Fin k)
    {r η : ℝ} (hη : 0 ≤ η)
    (hdiag : ∀ s, r ≤ RCLike.re (completedPairing D (a i s) (T (u s))))
    (hcross : ∀ j s t, (j,s) ≠ (i,t) → ‖completedPairing D (a j s) (T (u t))‖ ≤ η) :
    r - ((k : ℝ)+1)*N*η ≤ RCLike.re
      ((∑ j, completedPairing D (averagedPairFunctional (a j)))
        (T (normalizedPairSum (𝕜 := 𝕜) u))) := by
  classical
  let v := T (normalizedPairSum (𝕜 := 𝕜) u)
  let f (j : Fin k) := completedPairing D (averagedPairFunctional (a j))
  have hrow (s : Fin N) :
      ∑ t ∈ Finset.univ.erase s, ‖completedPairing D (a i s) (T (u t))‖ ≤ N*η := by
    calc
      _ ≤ ∑ _t ∈ Finset.univ.erase s, η := Finset.sum_le_sum (fun t ht =>
        hcross i s t (fun he => (Finset.ne_of_mem_erase ht) (congrArg Prod.snd he).symm))
      _ ≤ ∑ _t : Fin N, η := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun _ _ _ => hη)
      _ = N*η := by simp
  have hself : r-N*η ≤ RCLike.re (f i v) :=
    normalizedPairSum_re_lower_bound D hN (a i) u T hdiag hrow
  have hother (j : Fin k) (hj : j ≠ i) : ‖f j v‖ ≤ N*η := by
    exact normalizedPairSum_norm_le_of_entry_bounds D hN (a j) u T
      (fun s t => hcross j s t (fun he => hj (congrArg Prod.fst he)))
  have hsum : ∑ j ∈ Finset.univ.erase i, ‖f j v‖ ≤ k*(N*η) := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, N*η := Finset.sum_le_sum
        (fun j hj => hother j (Finset.ne_of_mem_erase hj))
      _ ≤ ∑ _j : Fin k, N*η := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) hη)
      _ = k*(N*η) := by simp
  have herr := sum_functionals_apply_sub_diagonal_norm_le f (fun _ => v) i hsum
  have hre := RCLike.re_le_norm (f i v-(∑ j,f j) v)
  rw [map_sub,norm_sub_rev] at hre
  change r-((k : ℝ)+1)*N*η ≤ RCLike.re ((∑ j,f j) v)
  nlinarith

end ThesisCommon.GowersMaurey
