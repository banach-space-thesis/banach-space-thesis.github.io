import NonCalkinAlgebra.TwistedAveraging
import NonCalkinAlgebra.TwistedCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.TwistedRegular
universe u
variable {G : Type u} [AddCommGroup G]

/-- Properties retained by each finite composition of the actual averages. -/
structure AveragingProperties (c : Cocycle G)
    (T : closedSubalgebra c →L[ℂ] closedSubalgebra c) : Prop where
  norm_le : ∀ a, ‖T a‖ ≤ ‖a‖
  map_one : T 1 = 1
  ideal_mem : ∀ (I : TwoSidedIdeal (closedSubalgebra c)) (a : closedSubalgebra c),
    a ∈ I → T a ∈ I

theorem finiteAveraging (c : Cocycle G)
    (hnd : ∀ g : G, g ≠ 0 → ∃ h : G, c h g + c g h ≠ 0) (s : Finset G) :
    ∃ T : closedSubalgebra c →L[ℂ] closedSubalgebra c,
      AveragingProperties c T ∧
      ∀ g ∈ s, g ≠ 0 → T (shiftInAlgebra c g) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨ContinuousLinearMap.id ℂ _, ⟨fun _ => le_rfl, rfl, fun _ _ ha => ha⟩,
      fun g hg => False.elim (Finset.notMem_empty g hg)⟩
  | @insert g s hg ih =>
    obtain ⟨T, hT, hkill⟩ := ih
    by_cases hg0 : g = 0
    · refine ⟨T, hT, ?_⟩
      intro k hk hk0
      rcases Finset.mem_insert.mp hk with hkg | hks
      · exact False.elim (hk0 (hkg.trans hg0))
      · exact hkill k hks hk0
    · obtain ⟨h, hh⟩ := hnd g hg0
      refine ⟨T.comp (averageShift c h), ?_, ?_⟩
      · exact ⟨fun a => (hT.norm_le _).trans (norm_averageShift_le c h a),
          by simp only [ContinuousLinearMap.comp_apply, averageShift_one, hT.map_one],
          fun I a ha => hT.ideal_mem I _ (averageShift_mem c h I ha)⟩
      · intro k hk hk0
        simp only [ContinuousLinearMap.comp_apply]
        rcases Finset.mem_insert.mp hk with hkg | hks
        · subst k
          rw [averageShift_shift_of_ne_zero c h g hh, map_zero]
        · rcases averageShift_shift_eq_zero_or_self c h k with hkilled | hfixed
          · rw [hkilled, map_zero]
          · rw [hfixed, hkill k hks hk0]

/-- A finite average sends any prescribed polynomial exactly to its constant
coefficient, while remaining contractive and preserving every two-sided ideal. -/
theorem existsAveraging_polynomial (c : Cocycle G)
    (hnd : ∀ g : G, g ≠ 0 → ∃ h : G, c h g + c g h ≠ 0)
    (a : closedSubalgebra c)
    (ha : a ∈ Submodule.span ℂ (Set.range (shiftInAlgebra c))) :
    ∃ T : closedSubalgebra c →L[ℂ] closedSubalgebra c,
      AveragingProperties c T ∧ T a = coefficientZero c a • (1 : closedSubalgebra c) := by
  classical
  rw [← Finsupp.range_linearCombination (v := shiftInAlgebra c) ℂ] at ha
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp ha
  rw [← hb]
  obtain ⟨T, hT, hkill⟩ := finiteAveraging c hnd b.support
  refine ⟨T, hT, ?_⟩
  have hgen : ∀ g ∈ b.support, T (shiftInAlgebra c g) =
      coefficientZero c (shiftInAlgebra c g) • (1 : closedSubalgebra c) := by
    intro g hg
    by_cases hg0 : g = 0
    · subst g
      rw [shiftInAlgebra_zero, hT.map_one, coefficientZero_one, one_smul]
    · rw [hkill g hg hg0, coefficientZero_shift_of_ne_zero c g hg0, zero_smul]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro g hg
  rw [hgen g hg, smul_smul]
  rfl

end NonCalkinAlgebra.TwistedRegular
