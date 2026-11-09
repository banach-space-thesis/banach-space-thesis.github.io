import NonCalkinAlgebra.TraceParameters
import NonCalkinAlgebra.TraceCoordinateValue
import NonCalkinAlgebra.TraceCoordinateSeparation
import NonCalkinAlgebra.ProductCompletedTrace
import NonCalkinAlgebra.RealMainReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000

namespace NonCalkinAlgebra
open FiniteBlockRefinement FiniteBlockRefinement.RootedBlockDiagram
open NormedStarDirectLimit TraceWeightRefinement
open scoped Matrix.Norms.L2Operator NormedStarCompletion

private structure TraceCodeParameters where
  Index : Type
  cardinal : Cardinal.mk Index = Cardinal.continuum
  theta : Index → ℝ
  positive : ∀ i, 0 < theta i ∧ theta i < 1
  independent : ∀ (S : Set Index) i, theta i ∈ Algebra.adjoin ℚ (theta '' S) ↔ i ∈ S

namespace TraceCodeParameters
variable (P : TraceCodeParameters) (S : Set P.Index)

private abbrev codeRing : Subring ℝ := (Algebra.adjoin ℚ (P.theta '' S)).toSubring

private theorem irrational (i : P.Index) (q : ℚ) : (q : ℝ) ≠ P.theta i := by
  intro h
  have hq : (q : ℝ) ∈ Algebra.adjoin ℚ (P.theta '' (∅ : Set P.Index)) :=
    (Algebra.adjoin ℚ (P.theta '' (∅ : Set P.Index))).algebraMap_mem q
  rw [h, P.independent] at hq
  exact hq

private def state (i : S) : State (P.codeRing S) :=
  State.initial (P.theta i) (P.positive i).1 (P.positive i).2
    ((P.independent S i).2 i.property) (P.irrational i)

private def diagrams : P.Index ⊕ S → RootedBlockDiagram
  | .inl _ => paddingDiagram
  | .inr i => parameterDiagram (P.state S i) rfl rfl

private def weights : ∀ i n, (P.diagrams S i).Color n → ℝ
  | .inl _, n, c => paddingWeight n c
  | .inr i, n, c => parameterWeight (P.state S i) n c

private theorem weights_root (i : P.Index ⊕ S) (c : (P.diagrams S i).Color 0) :
    P.weights S i 0 c = 1 := by
  cases i <;> rfl

private theorem weights_nonneg (i : P.Index ⊕ S) (n : ℕ) (c : (P.diagrams S i).Color n) :
    0 ≤ P.weights S i n c := by
  cases i with
  | inl i =>
    change 0 ≤ paddingWeight n c
    unfold paddingWeight
    split <;> norm_num
  | inr i => exact parameterWeight_nonneg _ _ _

private theorem weights_law (i : P.Index ⊕ S) (n : ℕ) :
    UniversalWeightLaw ((P.diagrams S i).step n) (P.weights S i n) (P.weights S i (n+1)) := by
  cases i with
  | inl i => exact paddingWeight_step n
  | inr i => exact parameterWeight_step (P.state S i) rfl rfl n

private theorem weights_mem (i : P.Index ⊕ S) (n : ℕ) (c : (P.diagrams S i).Color n) :
    P.weights S i n c ∈ P.codeRing S := by
  cases i with
  | inl i =>
    change paddingWeight n c ∈ P.codeRing S
    unfold paddingWeight
    split
    · exact (P.codeRing S).one_mem
    · change (1/2 : ℝ) ∈ Algebra.adjoin ℚ (P.theta '' S)
      have hhalf : algebraMap ℚ ℝ (1/2 : ℚ) = (1/2 : ℝ) := by norm_num
      rw [← hhalf]
      exact (Algebra.adjoin ℚ (P.theta '' S)).algebraMap_mem (1/2 : ℚ)
  | inr i => exact parameterWeight_mem _ _ _

private def coefficient : ComplexCStarAlgebra where
  Carrier := TensorLimit (P.diagrams S)
  normedRing := inferInstance
  normedAlgebra := inferInstance
  completeSpace := inferInstance
  nontrivial := NormOneClass.nontrivial
  starRing := inferInstance
  cstarRing := inferInstance
  starModule := inferInstance

private theorem coefficient_af : IsApproximatelyFiniteDimensional (P.coefficient S).Carrier :=
  tensorLimit_AF (P.diagrams S)

private theorem coefficient_simple : IsTopologicallySimple (P.coefficient S).Carrier := by
  apply tensorLimit_simple
  rintro (i | i)
  · exact paddingDiagram_mixes
  · exact parameterDiagram_mixes _ rfl rfl

private theorem coefficient_density :
    HasDensityCharacter (P.coefficient S).Carrier Cardinal.continuum := by
  have hne : Cardinal.mk P.Index ≠ 0 := by
    rw [P.cardinal]
    exact (Cardinal.aleph0_pos.trans_le Cardinal.aleph0_le_continuum).ne'
  letI : Nonempty P.Index := Cardinal.mk_ne_zero_iff.mp hne
  let e : P.Index ↪ P.Index ⊕ S := ⟨Sum.inl, Sum.inl_injective⟩
  let c (i : P.Index) : (P.diagrams S (e i)).Color 1 := PUnit.unit
  let r (i : P.Index) : (P.diagrams S (e i)).Row 1 (c i) := (0 : Fin 2)
  let s (i : P.Index) : (P.diagrams S (e i)).Row 1 (c i) := (1 : Fin 2)
  have hrs (i : P.Index) : r i ≠ s i := by
    change (0 : Fin 2) ≠ 1
    decide
  have hindex : Cardinal.mk (P.Index ⊕ S) ≤ Cardinal.continuum := by
    have hinf : Cardinal.aleph0 ≤ Cardinal.mk P.Index := by
      rw [P.cardinal]
      exact Cardinal.aleph0_le_continuum
    simp only [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.add_eq_max hinf]
    exact max_le P.cardinal.le ((Cardinal.mk_subtype_le _).trans P.cardinal.le)
  exact tensorLimit_density_of_separated (P.diagrams S) hindex P.cardinal
    (fun i => coordinateEmbedding (P.diagrams S) (e i) 1 (rankOne _ (c i) (r i)))
    (coordinate_projections_separated (P.diagrams S) e c r s hrs)

private theorem coefficient_code (i : P.Index) :
    (P.theta i : ℂ) ∈ commonIdempotentTraceValues (P.coefficient S).Carrier ↔ i ∈ S := by
  constructor
  · intro hi
    have h := tensorTrace_excludes (P.diagrams S) (P.weights S) (P.weights_root S)
      (P.weights_law S) (P.weights_nonneg S) (P.codeRing S) (P.weights_mem S) hi
    obtain ⟨t, ht, heq⟩ := h
    exact (P.independent S i).1 ((Complex.ofReal_injective heq) ▸ ht)
  · intro hi
    let j : S := ⟨i, hi⟩
    let s := P.state S j
    let B := parameterDiagram s rfl rfl
    let g (n : ℕ) : Blocks (B.Row n) →⋆ₐ[ℂ] (P.coefficient S).Carrier :=
      coordinateEmbedding (P.diagrams S) (Sum.inr j) n
    let p := rankOne (B.Row 1) false (Classical.choice inferInstance)
    refine ⟨g 1 p, ?_, ?_⟩
    · rw [← map_mul, rankOne_sq]
    · intro σ hσ
      exact coordinate_trace_value s rfl rfl g
        (coordinateEmbedding_step (P.diagrams S) (Sum.inr j)) σ hσ

end TraceCodeParameters

universe v

/-- A simple unital AF coefficient algebra of density continuum avoiding both
operator quotients of every separable complex Banach space. -/
theorem AF_coefficient_existence : AFCoefficientExistenceStatement.{v} := by
  obtain ⟨J, θ, hJ, hθ, hind⟩ := exists_independent_trace_parameters
  let P : TraceCodeParameters := ⟨J, hJ, θ, hθ, hind⟩
  exact AF_coefficient_existence_of_common_trace_codes P.cardinal
    (fun i => (P.theta i : ℂ)) P.coefficient P.coefficient_code
    P.coefficient_af P.coefficient_density P.coefficient_simple

/-- The standalone complex conclusion of Theorem 1.1. -/
theorem main_theorem : MainStatement.{v} :=
  main_of_coefficient_existence (coefficient_existence_of_AF AF_coefficient_existence)

/-- The real conclusion of Remark 1.2. -/
theorem real_main_theorem : RealMainStatement.{v} :=
  real_main_of_complex_main main_theorem

end NonCalkinAlgebra
