import Sigma.CrossedDualProjection
import Sigma.ReducedAtoms

/-! Compress the symmetric and antisymmetric pairs in the crossed dual.
The singleton infinity coordinate is retained with weight one. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

def EnumeratedConstruction.reducedCoefficients (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) : lp (fun _ : ReducedAtom => ℝ) 1 :=
  let c := lpOneComap (reducedAtomEmbedding side) (D.coefficients (D.extendCrossedFunctional side φ))
  (2 : ℝ) • c - lpOneRestrict {Sum.inr ()} c

theorem EnumeratedConstruction.reducedCoefficients_pair (D : EnumeratedConstruction) (side copy : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) (q : ℕ ⊕ ConstructionIndex) :
    D.reducedCoefficients side φ (.inl (copy,q)) =
      2 * D.coefficients (D.extendCrossedFunctional side φ) (copy,pairedAtom q false) := by
  simp [reducedCoefficients,lpOneRestrict_apply]

theorem EnumeratedConstruction.reducedCoefficients_infinity (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) :
    D.reducedCoefficients side φ (.inr ()) =
      D.coefficients (D.extendCrossedFunctional side φ) (!side,.inr (.inr ())) := by
  simp only [reducedCoefficients,lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,lpOneRestrict_apply,Set.mem_singleton_iff,ite_true,lpOneComap_apply,
    reducedAtomEmbedding_infinity]
  ring

theorem EnumeratedConstruction.reducedCoefficients_add (D : EnumeratedConstruction) (side : Bool)
    (φ ψ : FinalCandidate D side →L[ℝ] ℝ) :
    D.reducedCoefficients side (φ+ψ) = D.reducedCoefficients side φ + D.reducedCoefficients side ψ := by
  apply lp.ext
  funext p
  rcases p with ⟨copy,q⟩ | ⟨⟩
  · simp only [lp.coeFn_add,Pi.add_apply,D.reducedCoefficients_pair,extendCrossedFunctional,
      ContinuousLinearMap.add_comp,D.coefficients_add]
    change 2 * (_ + _) = 2 * _ + 2 * _
    ring
  · simp only [lp.coeFn_add,Pi.add_apply,D.reducedCoefficients_infinity,extendCrossedFunctional,
      ContinuousLinearMap.add_comp,D.coefficients_add]

theorem EnumeratedConstruction.reducedCoefficients_smul (D : EnumeratedConstruction) (side : Bool)
    (r : ℝ) (φ : FinalCandidate D side →L[ℝ] ℝ) :
    D.reducedCoefficients side (r • φ) = r • D.reducedCoefficients side φ := by
  apply lp.ext
  funext p
  rcases p with ⟨copy,q⟩ | ⟨⟩
  · simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,D.reducedCoefficients_pair,extendCrossedFunctional,
      ContinuousLinearMap.smul_comp,D.coefficients_smul]
    change 2 * (r * _) = r * (2 * _)
    ring
  · simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,D.reducedCoefficients_infinity,extendCrossedFunctional,
      ContinuousLinearMap.smul_comp,D.coefficients_smul]

theorem EnumeratedConstruction.reducedCoefficients_norm_le (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) : ‖D.reducedCoefficients side φ‖ ≤ 3 * ‖φ‖ := by
  let c := lpOneComap (reducedAtomEmbedding side) (D.coefficients (D.extendCrossedFunctional side φ))
  have hc : ‖c‖ ≤ ‖φ‖ := by
    calc
      ‖c‖ ≤ ‖D.coefficients (D.extendCrossedFunctional side φ)‖ := lpOneComap_norm_le _ _
      _ = ‖φ‖ := by rw [D.coefficients_norm,D.extendCrossedFunctional_norm]
  have hm := lpOneRestrict_norm_le {Sum.inr ()} c
  change ‖(2 : ℝ) • c - lpOneRestrict {Sum.inr ()} c‖ ≤ _
  calc
    _ ≤ ‖(2 : ℝ) • c‖ + ‖lpOneRestrict {Sum.inr ()} c‖ := norm_sub_le _ _
    _ ≤ 3 * ‖φ‖ := by rw [norm_smul]; norm_num; linarith

def EnumeratedConstruction.synthesizeReduced (D : EnumeratedConstruction) (side : Bool)
    (c : lp (fun _ : ReducedAtom => ℝ) 1) : FinalCandidate D side →L[ℝ] ℝ :=
  (D.fullCoefficientEquiv.symm (lpExtend (𝕜 := ℝ) 1 (reducedAtomEmbedding side) c)).comp
    (D.crossedInjection side)

theorem EnumeratedConstruction.synthesizeReduced_norm_le (D : EnumeratedConstruction) (side : Bool)
    (c : lp (fun _ : ReducedAtom => ℝ) 1) : ‖D.synthesizeReduced side c‖ ≤ ‖c‖ := by
  let φ := D.fullCoefficientEquiv.symm (lpExtend (𝕜 := ℝ) 1 (reducedAtomEmbedding side) c)
  have hφ : ‖φ‖ ≤ ‖c‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right
        (norm_lpExtend_le (𝕜 := ℝ) (X := ℝ) (p := 1) (reducedAtomEmbedding side)) (norm_nonneg c))
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
  intro f
  change ‖φ (D.crossedInjection side f)‖ ≤ _
  calc
    _ ≤ ‖φ‖ * ‖D.crossedInjection side f‖ := φ.le_opNorm _
    _ ≤ ‖c‖ * ‖f‖ := by rw [D.crossedInjection_norm]; exact mul_le_mul_of_nonneg_right hφ (norm_nonneg f)

end SigmaNonprimarity
