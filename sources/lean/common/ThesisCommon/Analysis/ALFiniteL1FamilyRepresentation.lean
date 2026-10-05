import ThesisCommon.Analysis.ALBandDecomposition
import ThesisCommon.Analysis.ALPrincipalL1Representation
import ThesisCommon.Analysis.ALDedekindComplete
import ThesisCommon.Analysis.IntervalLpFunctionSelfSimilarity

/-! The constructive real Kakutani representation before measure coproduct
assembly: every complete AL-lattice is the ordered ell-one sum of actual
finite-measure L1 spaces in the same universe. -/
noncomputable section
universe u
open Set MeasureTheory
namespace ThesisCommon
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] [HasSolidNorm E] [CompleteSpace E] in
theorem booleanStonePoint_nonempty_of_positive_ne_zero (e : E) [Fact (0 ≤ e)] (he : e ≠ 0) :
    Nonempty (BooleanStonePoint (PositiveFragmentAlgebra e)) := by
  have htop : (⊤ : PositiveFragmentAlgebra e) ≠ ⊥ := by
    intro h
    apply he
    simpa only [positiveFragmentValue_top, positiveFragmentValue_bot] using
      congrArg positiveFragmentValue h
  obtain ⟨p, _⟩ := (booleanStoneSet_nonempty_iff (⊤ : PositiveFragmentAlgebra e)).mpr htop
  exact ⟨p⟩

include hAL in
theorem exists_ordered_lp_finite_L1_of_AL :
    ∃ (I : Type u) (X : I → Type u) (m : ∀ i, MeasurableSpace (X i)),
      letI := m
      ∃ μ : ∀ i, Measure (X i), (∀ i, IsFiniteMeasure (μ i)) ∧ (∀ i, Nonempty (X i)) ∧
        ∃ d : E ≃ₗᵢ[ℝ] lp (fun i => Lp ℝ 1 (μ i)) 1,
          ∀ x : E, 0 ≤ x ↔ ∀ i, 0 ≤ d x i := by
  letI : ConditionallyCompleteLattice E := alConditionallyCompleteLattice hAL
  obtain ⟨S, hpos, hdis, htotal⟩ := exists_total_positive_disjoint_family (E := E)
  let a : S → E := Subtype.val
  have ha : ∀ i, 0 ≤ a i := fun i => (hpos i i.property).1
  have hd : Pairwise (fun i j : S => |a i| ⊓ |a j| = 0) := by
    intro i j hij
    rw [abs_of_nonneg (ha i), abs_of_nonneg (ha j)]
    exact hdis i.property j.property (fun h => hij (Subtype.ext h))
  have ht : ∀ x : E, 0 ≤ x → (∀ i, x ⊓ a i = 0) → x = 0 := by
    intro x hx hh
    exact htotal x hx (fun e he => hh ⟨e, he⟩)
  letI (i : S) : Fact (0 ≤ a i) := ⟨ha i⟩
  let X : S → Type u := fun i => BooleanStonePoint (PositiveFragmentAlgebra (a i))
  let μ : ∀ i, Measure (X i) := fun i => alFragmentMeasure hAL (a i)
  let b := alBandIsometryEquiv hAL a ha hd ht
  let c : lp (fun i => principalBand (a i)) 1 ≃ₗᵢ[ℝ] lp (fun i => Lp ℝ 1 (μ i)) 1 :=
    lebesgueLpCoordinateEquiv (by norm_num) (fun i => (alPrincipalL1Equiv hAL (a i)).symm)
  refine ⟨S, X, inferInstance, μ, fun i => inferInstance, ?_, b.trans c, ?_⟩
  · intro i
    exact booleanStonePoint_nonempty_of_positive_ne_zero (a i) (hpos i i.property).2
  · intro x
    have hc (i : S) : 0 ≤ (b.trans c) x i ↔ 0 ≤ b x i := by
      change 0 ≤ (alPrincipalL1Equiv hAL (a i)).symm (b x i) ↔ 0 ≤ b x i
      have h := alPrincipalL1Equiv_nonneg_iff hAL (a i)
        ((alPrincipalL1Equiv hAL (a i)).symm (b x i))
      rw [LinearIsometryEquiv.apply_symm_apply] at h
      exact h.symm
    simp only [hc]
    exact alBandIsometryEquiv_nonneg_iff hAL a ha hd ht x

end ThesisCommon
