import ThesisCommon.Analysis.ALMaximalDisjointFamily
import ThesisCommon.Analysis.ALRenormBandEstimates
import ThesisCommon.Analysis.ALOrderCompleteness
import ThesisCommon.Analysis.LpOneFamilyOperators
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Contractive coordinates and synthesis for arbitrary disjoint principal
bands in a complete real AL-lattice. -/
noncomputable section
open Set
open scoped Classical ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (a : I → E) (hd : Pairwise (fun i j => |a i| ⊓ |a j| = 0))

include hd in
theorem alBandProjection_finite_sum_le (s : Finset I) (x : E) (hx : 0 ≤ x) :
    ∑ i ∈ s, principalBandProjection (a i) x ≤ x :=
  positive_orthogonal_sum_le (fun i => principalBandProjection (a i))
    (fun i => principalBandProjection_nonneg (a i))
    (fun i => principalBandProjection_le_id (a i))
    (fun _ _ hij x => principalBandProjection_orthogonal (hd hij) x) s x hx

include hAL hd in
theorem alBandProjection_finite_sum_norm_le (s : Finset I) (x : E) :
    ∑ i ∈ s, ‖principalBandProjection (a i) x‖ ≤ ‖x‖ := by
  have hpos (i : I) : 0 ≤ principalBandProjection (a i) |x| :=
    principalBandProjection_nonneg (a i) |x| (abs_nonneg x)
  calc
    (∑ i ∈ s, ‖principalBandProjection (a i) x‖) =
        ∑ i ∈ s, ‖principalBandProjection (a i) |x|‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [principalBandProjection_abs, norm_abs_eq_norm]
    _ = ‖∑ i ∈ s, principalBandProjection (a i) |x|‖ :=
      (al_norm_sum hAL s _ (fun i _ => hpos i)).symm
    _ ≤ ‖|x|‖ := by
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => hpos i)), abs_abs]
      exact alBandProjection_finite_sum_le a hd s |x| (abs_nonneg x)
    _ = ‖x‖ := norm_abs_eq_norm x

include hAL hd in
theorem alBandProjection_summable_norm (x : E) :
    Summable (fun i => ‖principalBandProjection (a i) x‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _)
    (fun s => alBandProjection_finite_sum_norm_le hAL a hd s x)

def alBandCoefficients (x : E) : lp (fun i => principalBand (a i)) 1 :=
  ⟨fun i => ⟨principalBandProjection (a i) x, (principalBand_orderClosed (a i)).bandProjection_mem x⟩,
    memℓp_gen (by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using
        alBandProjection_summable_norm hAL a hd x)⟩

theorem alBandCoefficients_norm_le (x : E) : ‖alBandCoefficients hAL a hd x‖ ≤ ‖x‖ := by
  rw [← (lpOneFamily_hasSum_norm (alBandCoefficients hAL a hd x)).tsum_eq]
  exact (alBandProjection_summable_norm hAL a hd x).tsum_le_of_sum_le
    (fun s => alBandProjection_finite_sum_norm_le hAL a hd s x)

def alBandCoordinates : E →L[ℝ] lp (fun i => principalBand (a i)) 1 :=
  LinearMap.mkContinuous
    { toFun := alBandCoefficients hAL a hd
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        exact Subtype.ext (map_add (principalBandProjection (a i)) x y)
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        exact Subtype.ext (map_smul (principalBandProjection (a i)) c x) }
    1 (fun x => by simpa only [one_mul] using alBandCoefficients_norm_le hAL a hd x)

theorem alBandCoordinates_apply (x : E) (i : I) :
    (alBandCoordinates hAL a hd x i : E) = principalBandProjection (a i) x := rfl

variable [CompleteSpace E]

def alBandSynthesis : lp (fun i => principalBand (a i)) 1 →L[ℝ] E :=
  lpOneFamilyOperator (fun i => (principalBand (a i)).subtypeL) 1 zero_le_one
    (fun _ => Submodule.norm_subtypeL_le _)

theorem alBandSynthesis_apply (x : lp (fun i => principalBand (a i)) 1) :
    alBandSynthesis a x = ∑' i, (x i : E) := rfl

theorem alBandSynthesis_norm_le (x : lp (fun i => principalBand (a i)) 1) :
    ‖alBandSynthesis a x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using
    (alBandSynthesis a).le_of_opNorm_le (norm_lpOneFamilyOperator_le _ _ zero_le_one _) x

theorem alBandSynthesis_summable (x : lp (fun i => principalBand (a i)) 1) :
    Summable (fun i => (x i : E)) := by
  have h : Summable (fun i => ‖(x i : E)‖) := (lpOneFamily_hasSum_norm x).summable
  exact h.of_norm

include hd in
theorem principalBandProjection_alBandSynthesis (x : lp (fun i => principalBand (a i)) 1)
    (i : I) : principalBandProjection (a i) (alBandSynthesis a x) = x i := by
  rw [alBandSynthesis_apply, (principalBandProjection (a i)).map_tsum (alBandSynthesis_summable a x),
    tsum_eq_single i]
  · exact (principalBand_orderClosed (a i)).bandProjection_eq_self (x i).property
  · intro j hji
    apply (principalBandProjection_eq_zero_iff _ _).mpr
    rw [inf_comm]
    exact principalBand_disjoint_of_disjoint (hd (Ne.symm hji))
      (self_mem_principalBand (a i)) (x j).property

theorem alBandCoordinates_alBandSynthesis (x : lp (fun i => principalBand (a i)) 1) :
    alBandCoordinates hAL a hd (alBandSynthesis a x) = x := by
  apply lp.ext
  funext i
  apply Subtype.ext
  exact principalBandProjection_alBandSynthesis a hd x i

end ThesisCommon
