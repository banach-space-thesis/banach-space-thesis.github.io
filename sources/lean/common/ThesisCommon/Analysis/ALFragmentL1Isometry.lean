import ThesisCommon.Analysis.ALFragmentL1Map
import ThesisCommon.Analysis.ALRefinementPrincipal
import ThesisCommon.Analysis.ALOrderCompleteness
import ThesisCommon.Analysis.LatticeDisjointFinite

/-! Norm preservation for the actual Stone L1 map. The proof uses finite
disjoint value cells of simple functions and their density in L1. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem lattice_disjoint_smul_smul {x y : E} (h : |x| ⊓ |y| = 0) (r s : ℝ) :
    |r • x| ⊓ |s • y| = 0 := by
  have hx : x ∈ latticeDisjointComplement ({y} : Set E) := by
    intro z hz
    simpa only [Set.mem_singleton_iff.mp hz] using h
  have hrx := (latticeDisjointComplement ({y} : Set E)).smul_mem r hx
  have hy : y ∈ latticeDisjointComplement ({r • x} : Set E) := by
    intro z hz
    rw [Set.mem_singleton_iff.mp hz, inf_comm]
    exact hrx y (Set.mem_singleton y)
  have hsy := (latticeDisjointComplement ({r • x} : Set E)).smul_mem s hy
  rw [inf_comm]
  exact hsy (r • x) (Set.mem_singleton _)

variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
include hAL

omit [CompleteSpace E] [NormedSpace ℝ E] [IsOrderedModule ℝ E] in
theorem al_norm_sum_of_pairwise_disjoint {ι : Type*} (F : Finset ι) (v : ι → E)
    (hd : (↑F : Set ι).Pairwise (fun i j => |v i| ⊓ |v j| = 0)) :
    ‖∑ i ∈ F, v i‖ = ∑ i ∈ F, ‖v i‖ := by
  calc
    ‖∑ i ∈ F, v i‖ = ‖|∑ i ∈ F, v i|‖ := (norm_abs_eq_norm _).symm
    _ = ‖∑ i ∈ F, |v i|‖ := congrArg norm (lattice_abs_sum_of_pairwise_disjoint F v hd)
    _ = ∑ i ∈ F, ‖|v i|‖ := al_norm_sum hAL F _ (fun _ _ => abs_nonneg _)
    _ = ∑ i ∈ F, ‖v i‖ := by simp only [norm_abs_eq_norm]

variable (e : E) [Fact (0 ≤ e)]

theorem alFragmentL1Map_norm_simple
    (f : Lp.simpleFunc ℝ 1 (alFragmentMeasure hAL e)) :
    ‖alFragmentL1Map hAL e f‖ = ‖f‖ := by
  let g := Lp.simpleFunc.toSimpleFunc f
  let v (r : ℝ) := positiveFragmentValue (alMeasurableFragment hAL e
    (g ⁻¹' {r}) (g.measurableSet_fiber r))
  have hd : (↑g.range : Set ℝ).Pairwise (fun r s => |r • v r| ⊓ |s • v s| = 0) := by
    intro r _ s _ hrs
    apply lattice_disjoint_smul_smul
    rw [abs_of_nonneg (positiveFragmentValue_nonneg _),
      abs_of_nonneg (positiveFragmentValue_nonneg _)]
    apply positiveFragmentValue_disjoint
    apply alMeasurableFragment_disjoint
    apply Set.disjoint_left.mpr
    intro x hxr hxs
    exact hrs (hxr.symm.trans hxs)
  have heq : alFragmentL1Map hAL e f = ∑ r ∈ g.range, r • v r := by
    rw [alFragmentL1Map, L1.setToL1_eq_setToL1SCLM]
    change (∑ r ∈ g.range, alFragmentVectorContent hAL e (g ⁻¹' {r}) r) = _
    apply Finset.sum_congr rfl
    intro r _
    exact alFragmentVectorContent_apply hAL e _ (g.measurableSet_fiber r) r
  rw [heq, al_norm_sum_of_pairwise_disjoint hAL _ _ hd, L1.SimpleFunc.norm_eq_sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [norm_smul, norm_alMeasurableFragment]
  exact mul_comm _ _

theorem alFragmentL1Map_norm (f : Lp ℝ 1 (alFragmentMeasure hAL e)) :
    ‖alFragmentL1Map hAL e f‖ = ‖f‖ := by
  refine (Lp.simpleFunc.denseRange (E := ℝ) (p := 1) (μ := alFragmentMeasure hAL e)
    (by norm_num)).induction_on f ?_ ?_
  · exact isClosed_eq (alFragmentL1Map hAL e).continuous.norm continuous_norm
  · exact alFragmentL1Map_norm_simple hAL e

def alFragmentL1Isometry : Lp ℝ 1 (alFragmentMeasure hAL e) →ₗᵢ[ℝ] E :=
  { (alFragmentL1Map hAL e).toLinearMap with norm_map' := alFragmentL1Map_norm hAL e }

end ThesisCommon
