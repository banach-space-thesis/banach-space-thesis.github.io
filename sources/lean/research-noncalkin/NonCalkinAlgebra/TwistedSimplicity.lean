import NonCalkinAlgebra.TwistedFiniteAveraging
import NonCalkinAlgebra.TwistedSpanDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.TwistedRegular
universe u
variable {G : Type u} [AddCommGroup G]

/-- Closed ideals contain the constant coefficient of each of their elements.
Finite averages depend on the approximating polynomial; no convergence of a
single chosen sequence of averaging maps is assumed. -/
theorem coefficient_smul_one_mem (c : Cocycle G)
    (hnd : ∀ g : G, g ≠ 0 → ∃ h : G, c h g + c g h ≠ 0)
    (I : TwoSidedIdeal (closedSubalgebra c)) (hI : IsClosed (I : Set (closedSubalgebra c)))
    (a : closedSubalgebra c) (ha : a ∈ I) :
    coefficientZero c a • (1 : closedSubalgebra c) ∈ I := by
  have hc : coefficientZero c a • (1 : closedSubalgebra c) ∈
      closure (I : Set (closedSubalgebra c)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp (dense_innerSpan c a)
      (ε / 4) (by positivity)
    obtain ⟨T, hT, hbT⟩ := existsAveraging_polynomial c hnd b hb
    refine ⟨T a, hT.ideal_mem I a ha, ?_⟩
    have hnorm : ‖a - b‖ < ε / 4 := by simpa only [dist_eq_norm] using hdist
    have hfirst : ‖T a - T b‖ ≤ ‖a - b‖ := by
      rw [← map_sub]
      exact hT.norm_le _
    have hsecond : ‖T b - coefficientZero c a • (1 : closedSubalgebra c)‖ ≤ ‖a - b‖ := by
      rw [hbT, ← sub_smul, norm_smul, norm_one, mul_one, ← map_sub]
      exact (norm_coefficientZero_le c (b - a)).trans_eq (norm_sub_rev b a)
    calc
      dist (coefficientZero c a • (1 : closedSubalgebra c)) (T a) =
          ‖T a - coefficientZero c a • (1 : closedSubalgebra c)‖ := by
        rw [dist_comm, dist_eq_norm]
      _ ≤ ‖T a - T b‖ + ‖T b - coefficientZero c a • (1 : closedSubalgebra c)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖a - b‖ + ‖a - b‖ := add_le_add hfirst hsecond
      _ < ε := by linarith
  rw [hI.closure_eq] at hc
  exact hc

/-- Nondegeneracy of the alternating cocycle proves topological simplicity
of the concrete closed twisted regular algebra. -/
theorem isTopologicallySimple_of_nondegenerate (c : Cocycle G)
    (hnd : ∀ g : G, g ≠ 0 → ∃ h : G, c h g + c g h ≠ 0) :
    IsTopologicallySimple (closedSubalgebra c) := by
  intro I hI
  by_cases hzero : I = ⊥
  · exact Or.inl hzero
  right
  have hex : ∃ a : closedSubalgebra c, a ∈ I ∧ a ≠ 0 := by
    by_contra! h
    apply hzero
    apply le_antisymm _ bot_le
    intro a ha
    simpa only [TwoSidedIdeal.mem_bot] using h a ha
  obtain ⟨a, ha, hane⟩ := hex
  have hcoef : coefficientZero c (star a * a) ≠ 0 := by
    intro h
    exact hane ((coefficientZero_star_mul_self_eq_zero_iff c a).mp h)
  have hconstant := coefficient_smul_one_mem c hnd I hI (star a * a)
    (I.mul_mem_left (star a) a ha)
  have hone : (1 : closedSubalgebra c) ∈ I := by
    have hm := twoSidedIdeal_smul_mem I hconstant (coefficientZero c (star a * a))⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ hcoef, one_smul] using hm
  apply le_antisymm le_top
  intro b hb
  simpa only [mul_one] using I.mul_mem_left b 1 hone

end NonCalkinAlgebra.TwistedRegular
