import ThesisCommon.Analysis.GowersMaureyEndomorphismSeminorm
import ThesisCommon.Analysis.GowersMaureyShiftDefects

/-! Operators determined by finitely many input coordinates have zero
block seminorm. This elementary statement uses actual eventual coordinate
vanishing of successive sequences and does not assume a shrinking basis
or assert that every finite-rank operator has this form. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BlockTestSequence.eventually_coordinate_zero
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (k : ℕ) : ∀ᶠ i : ℕ in atTop, u.vector i k = 0 := by
  by_cases hex : ∃ i, u.vector i k ≠ 0
  · obtain ⟨i, hi⟩ := hex
    filter_upwards [eventually_gt_atTop i] with j hij
    by_contra hj
    exact Nat.lt_irrefl k (u.successive i j hij k (Finsupp.mem_support_iff.mpr hi)
      k (Finsupp.mem_support_iff.mpr hj))
  · exact Eventually.of_forall (by simpa only [not_exists, not_not] using hex)

theorem BlockTestSequence.eventually_coordinates_zero
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (s : Finset ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ k ∈ s, u.vector i k = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hks ih =>
    filter_upwards [u.eventually_coordinate_zero k, ih] with i hi his
    simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hi his

theorem spaceOperatorSeminorm_eq_zero_of_tail_vanishing (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (B : ℕ)
    (hT : ∀ x : C00 𝕜, (∀ k ≤ B, x k = 0) → T (denseEmbedding D x) = 0) :
    spaceOperatorSeminorm D T = 0 := by
  apply le_antisymm _ (apply_nonneg (spaceOperatorSeminorm D) T)
  rw [spaceOperatorSeminorm_apply]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  have hz : (fun i => ‖T (denseEmbedding D (u.vector i))‖) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [u.eventually_coordinates_zero (Finset.range (B+1))] with i hi
    rw [hT _ (fun k hk => hi k (Finset.mem_range.mpr (by omega))), norm_zero]
  change limsup (fun i => ‖T (denseEmbedding D (u.vector i))‖) atTop ≤ 0
  rw [limsup_congr hz, limsup_const]

theorem spaceOperatorSeminorm_coordinate_smulRight (D : ConstructionData 𝕜)
    (k : ℕ) (x : ShiftSpace D) :
    spaceOperatorSeminorm D ((completedCoordinate D k).smulRight x) = 0 := by
  apply spaceOperatorSeminorm_eq_zero_of_tail_vanishing D _ k
  intro a ha
  simp only [ContinuousLinearMap.smulRight_apply, completedCoordinate_denseEmbedding]
  change a k • x = 0
  rw [ha k le_rfl, zero_smul]

theorem spaceOperatorSeminorm_shift_defect (D : ConstructionData 𝕜) :
    spaceOperatorSeminorm D (ContinuousLinearMap.id 𝕜 (ShiftSpace D) -
      (completedSpread D 0 1).comp (completedSpread D 1 0)) = 0 := by
  rw [completedSpread_right_left_defect]
  exact spaceOperatorSeminorm_coordinate_smulRight D 0 _

theorem spaceOperatorSeminorm_eq_zero_of_basis_tail (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (B : ℕ)
    (hT : ∀ j, B < j → T (basisVector D j) = 0) :
    spaceOperatorSeminorm D T = 0 := by
  classical
  apply spaceOperatorSeminorm_eq_zero_of_tail_vanishing D T B
  intro x hx
  have he : denseEmbedding D x = ∑ j ∈ x.support, x j • basisVector D j := by
    simp only [basisVector, ← map_smul, ← map_sum]
    apply congrArg (denseEmbedding D)
    change x = ∑ j ∈ x.support, x j • Finsupp.single j (1 : 𝕜)
    simpa only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]
      using (Finsupp.sum_single x).symm
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hBj : B < j := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hj (hx j (by omega))
  rw [map_smul, hT j hBj, smul_zero]

end ThesisCommon.GowersMaurey
