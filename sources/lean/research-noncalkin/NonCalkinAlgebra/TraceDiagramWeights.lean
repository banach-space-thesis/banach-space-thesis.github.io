import NonCalkinAlgebra.TraceParameterRefinements
import NonCalkinAlgebra.TracePaddingDiagram
import NonCalkinAlgebra.DiagramTraceLaw

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.TraceWeightRefinement
open NonCalkinAlgebra.FiniteBlockRefinement

variable {R : Subring ℝ}

def stateWeight (s : State R) : Bool → ℝ
  | false => s.leftWeight
  | true => s.rightWeight

theorem stateWeight_mem (s : State R) (c : Bool) : stateWeight s c ∈ R := by
  cases c
  · exact s.leftWeight_mem
  · exact s.rightWeight_mem

theorem stateWeight_nonneg (s : State R) (c : Bool) : 0 ≤ stateWeight s c := by
  cases c
  · exact s.leftWeight_pos.le
  · exact s.rightWeight_pos.le

private theorem left_law (s : State R) (h : s.rightWeight < s.leftWeight) :
    UniversalWeightLaw (leftRefinement s.leftDim s.rightDim) (stateWeight s)
      (stateWeight (s.subtractLeft h)) := by
  letI (d : Bool) : Fintype ((leftRefinement s.leftDim s.rightDim).Copies d) := by
    cases d
    · exact inferInstanceAs (Fintype PUnit.{1})
    · exact inferInstanceAs (Fintype Bool)
  apply UniversalWeightLaw.of_law
  intro c
  cases c <;> simp [leftRefinement, stateWeight, State.subtractLeft, Fintype.sum_bool,
    Fintype.sum_unique]

private theorem right_law (s : State R) (h : s.leftWeight < s.rightWeight) :
    UniversalWeightLaw (rightRefinement s.leftDim s.rightDim) (stateWeight s)
      (stateWeight (s.subtractRight h)) := by
  letI (d : Bool) : Fintype ((rightRefinement s.leftDim s.rightDim).Copies d) := by
    cases d
    · exact inferInstanceAs (Fintype Bool)
    · exact inferInstanceAs (Fintype PUnit.{1})
  apply UniversalWeightLaw.of_law
  intro c
  cases c <;> simp [rightRefinement, stateWeight, State.subtractRight, Fintype.sum_bool,
    Fintype.sum_unique]

theorem parameterEdge_weightLaw (s : State R) :
    UniversalWeightLaw (parameterEdge s).refinement (stateWeight s)
      (stateWeight (parameterEdge s).target) := by
  by_cases h : s.rightWeight < s.leftWeight
  · have he : parameterEdge s =
      ⟨s.subtractLeft h, leftRefinement s.leftDim s.rightDim⟩ := dif_pos h
    rw [he]
    exact left_law s h
  · have hR := lt_of_le_of_ne (le_of_not_gt h) s.weights_ne
    have he : parameterEdge s =
      ⟨s.subtractRight hR, rightRefinement s.leftDim s.rightDim⟩ := dif_neg h
    rw [he]
    exact right_law s hR

def parameterWeight (s : State R) : ∀ n, ParamColors n → ℝ
  | 0, _ => 1
  | n+1, c => stateWeight (parameterStates s n) c

theorem parameterWeight_mem (s : State R) (n : ℕ) (c : ParamColors n) :
    parameterWeight s n c ∈ R := by
  cases n
  · exact R.one_mem
  · exact stateWeight_mem _ _

theorem parameterWeight_nonneg (s : State R) (n : ℕ) (c : ParamColors n) :
    0 ≤ parameterWeight s n c := by
  cases n
  · exact zero_le_one
  · exact stateWeight_nonneg _ _

theorem parameterWeight_step (s : State R) (hl : s.leftDim = 1) (hr : s.rightDim = 1)
    (n : ℕ) : UniversalWeightLaw ((parameterDiagram s hl hr).step n)
      (parameterWeight s n) (parameterWeight s (n+1)) := by
  cases n with
  | succ n => exact parameterEdge_weightLaw (parameterStates s n)
  | zero =>
    let D := parameterDiagram s hl hr
    letI : Fintype (D.Color 0) := inferInstanceAs (Fintype Unit)
    letI : Fintype (D.Color 1) := inferInstanceAs (Fintype Bool)
    letI (d : D.Color 1) : Fintype ((D.step 0).Copies d) := inferInstanceAs (Fintype Unit)
    apply UniversalWeightLaw.of_law
    rintro ⟨⟩
    have h : s.leftWeight + s.rightWeight = 1 := by
      simpa [hl, hr] using s.normalized
    change (∑ d : Bool, ∑ _ : Unit,
      @ite ℝ ((() : Unit) = ()) (Classical.propDecidable _) (parameterWeight s 1 d) 0) = 1
    simpa [parameterWeight, parameterStates, stateWeight, Fintype.sum_bool, Fintype.sum_unique]
      using (add_comm s.rightWeight s.leftWeight).trans h

end NonCalkinAlgebra.TraceWeightRefinement

namespace NonCalkinAlgebra.FiniteBlockRefinement

theorem paddingWeight_step (n : ℕ) :
    UniversalWeightLaw (paddingDiagram.step n) (paddingWeight n) (paddingWeight (n+1)) := by
  cases n with
  | zero =>
    letI : Fintype (paddingDiagram.Color 0) := inferInstanceAs (Fintype PUnit.{1})
    letI : Fintype (paddingDiagram.Color 1) := inferInstanceAs (Fintype PUnit.{1})
    letI (d : paddingDiagram.Color 1) : Fintype ((paddingDiagram.step 0).Copies d) :=
      inferInstanceAs (Fintype (Fin 2))
    apply UniversalWeightLaw.of_law
    rintro ⟨⟩
    have hcol (d : paddingDiagram.Color 1) (k : (paddingDiagram.step 0).Copies d) :
        (paddingDiagram.step 0).color d k = PUnit.unit := rfl
    simp only [hcol, if_pos rfl]
    change (∑ _ : PUnit.{1}, ∑ _ : Fin 2, (1/2 : ℝ)) = 1
    norm_num
  | succ n =>
    exact UniversalWeightLaw.identity (P := PadRow (n+1)) (fun _ => (1/2 : ℝ))

end NonCalkinAlgebra.FiniteBlockRefinement
