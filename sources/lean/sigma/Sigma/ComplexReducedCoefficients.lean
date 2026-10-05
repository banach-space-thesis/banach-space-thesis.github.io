import Sigma.ComplexCrossedDualProjection
import Sigma.ReducedAtoms
import ThesisCommon.Analysis.SigmaComplexLpOneComap

/-! Compress the symmetric and antisymmetric pairs in the crossed dual.
The singleton infinity coordinate is retained with weight one. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem complexExtendReduced_pair_true (side copy : Bool) (q : ℕ ⊕ ConstructionIndex)
    (c : lp (fun _ : ReducedAtom => ℂ) 1) :
    lpExtend (𝕜 := ℂ) 1 (reducedAtomEmbedding side) c (copy,pairedAtom q true) = 0 := by
  change Function.extend (reducedAtomEmbedding side) c 0 (copy,pairedAtom q true) = 0
  exact Function.extend_apply' _ _ _ (pairedAtom_true_not_representative side copy q)

def ComplexEnumeratedConstruction.reducedCoefficients (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) : lp (fun _ : ReducedAtom => ℂ) 1 :=
  let c := complexLpOneComap (reducedAtomEmbedding side) (D.coefficients (D.extendCrossedFunctional side φ))
  (2 : ℂ) • c - JLMS.restrictL1 {Sum.inr ()} c

theorem ComplexEnumeratedConstruction.reducedCoefficients_pair (D : ComplexEnumeratedConstruction) (side copy : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) (q : ℕ ⊕ ConstructionIndex) :
    D.reducedCoefficients side φ (.inl (copy,q)) =
      2 * D.coefficients (D.extendCrossedFunctional side φ) (copy,pairedAtom q false) := by
  simp [reducedCoefficients,JLMS.restrictL1_apply]

theorem ComplexEnumeratedConstruction.reducedCoefficients_infinity (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) :
    D.reducedCoefficients side φ (.inr ()) =
      D.coefficients (D.extendCrossedFunctional side φ) (!side,.inr (.inr ())) := by
  simp only [reducedCoefficients,lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,JLMS.restrictL1_apply,Set.mem_singleton_iff,ite_true,complexLpOneComap_apply,
    reducedAtomEmbedding_infinity]
  ring

theorem ComplexEnumeratedConstruction.reducedCoefficients_add (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ ψ : ComplexFinalCandidate D side →L[ℂ] ℂ) :
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

theorem ComplexEnumeratedConstruction.reducedCoefficients_smul (D : ComplexEnumeratedConstruction) (side : Bool)
    (r : ℂ) (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) :
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

theorem ComplexEnumeratedConstruction.reducedCoefficients_norm_le (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) : ‖D.reducedCoefficients side φ‖ ≤ 3 * ‖φ‖ := by
  let c := complexLpOneComap (reducedAtomEmbedding side) (D.coefficients (D.extendCrossedFunctional side φ))
  have hc : ‖c‖ ≤ ‖φ‖ := by
    calc
      ‖c‖ ≤ ‖D.coefficients (D.extendCrossedFunctional side φ)‖ := complexLpOneComap_norm_le _ _
      _ = ‖φ‖ := by rw [D.coefficients_norm,D.extendCrossedFunctional_norm]
  have hm := JLMS.restrictL1_norm_le {Sum.inr ()} c
  change ‖(2 : ℂ) • c - JLMS.restrictL1 {Sum.inr ()} c‖ ≤ _
  calc
    _ ≤ ‖(2 : ℂ) • c‖ + ‖JLMS.restrictL1 {Sum.inr ()} c‖ := norm_sub_le _ _
    _ ≤ 3 * ‖φ‖ := by rw [norm_smul]; norm_num; linarith

def ComplexEnumeratedConstruction.synthesizeReduced (D : ComplexEnumeratedConstruction) (side : Bool)
    (c : lp (fun _ : ReducedAtom => ℂ) 1) : ComplexFinalCandidate D side →L[ℂ] ℂ :=
  (D.fullCoefficientEquiv.symm (lpExtend (𝕜 := ℂ) 1 (reducedAtomEmbedding side) c)).comp
    (D.crossedInjection side)

theorem ComplexEnumeratedConstruction.synthesizeReduced_norm_le (D : ComplexEnumeratedConstruction) (side : Bool)
    (c : lp (fun _ : ReducedAtom => ℂ) 1) : ‖D.synthesizeReduced side c‖ ≤ ‖c‖ := by
  let φ := D.fullCoefficientEquiv.symm (lpExtend (𝕜 := ℂ) 1 (reducedAtomEmbedding side) c)
  have hφ : ‖φ‖ ≤ ‖c‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right
        (norm_lpExtend_le (𝕜 := ℂ) (X := ℂ) (p := 1) (reducedAtomEmbedding side)) (norm_nonneg c))
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
  intro f
  change ‖φ (D.crossedInjection side f)‖ ≤ _
  calc
    _ ≤ ‖φ‖ * ‖D.crossedInjection side f‖ := φ.le_opNorm _
    _ ≤ ‖c‖ * ‖f‖ := by rw [D.crossedInjection_norm]; exact mul_le_mul_of_nonneg_right hφ (norm_nonneg f)

end SigmaNonprimarity


