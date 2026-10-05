import JFA.MainStatements
import JFA.InjectiveDecomposition

/-! Corollary 1.2. Extracting scalar components respects composition, so inverse
tensor operators give inverse scalar components. Conversely, tensor functoriality
transports a Banach-space isomorphism to the concrete injective completions. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
namespace JFA
universe u
section ScalarComposition
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G X : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G] [SeparableSpace G]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem epsilonScalarOperator_of_decomposition (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X)
    (V : E →L[𝕜] F) (S : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X)
    (hS : HasSeparableRange 𝕜 (InjectiveTensor 𝕜 E X) (InjectiveTensor 𝕜 F X) S)
    (hEq : ∀ e x, T (injectivePure 𝕜 E X e x) =
      injectivePure 𝕜 F X (V e) x + S (injectivePure 𝕜 E X e x)) : epsilonScalarOperator hX hfew T = V := by
  apply ContinuousLinearMap.ext
  intro e
  apply (NormedSpace.eq_iff_forall_dual_eq (𝕜 := 𝕜)).mpr
  intro φ
  rw [epsilonScalarOperator_spec]
  apply scalarCoefficient_eq hX hfew
    ((hS.comp_right (injectivePureMap e)).comp_left (leftSlice φ))
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (leftSlice φ) (hEq e x)
  simpa only [map_add, leftSlice_pure, sliceOperator, ContinuousLinearMap.comp_apply,
    injectivePureMap_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] using h

omit [CompleteSpace F] [SeparableSpace F] in
theorem epsilonScalarOperator_comp_of_decompositions
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X)
    (Q : InjectiveTensor 𝕜 F X →L[𝕜] InjectiveTensor 𝕜 G X)
    (U : E →L[𝕜] F) (V : F →L[𝕜] G)
    (S : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X)
    (R : InjectiveTensor 𝕜 F X →L[𝕜] InjectiveTensor 𝕜 G X)
    (hS : HasSeparableRange 𝕜 (InjectiveTensor 𝕜 E X) (InjectiveTensor 𝕜 F X) S)
    (hR : HasSeparableRange 𝕜 (InjectiveTensor 𝕜 F X) (InjectiveTensor 𝕜 G X) R)
    (hT : ∀ e x, T (injectivePure 𝕜 E X e x) =
      injectivePure 𝕜 F X (U e) x + S (injectivePure 𝕜 E X e x))
    (hQ : ∀ f x, Q (injectivePure 𝕜 F X f x) =
      injectivePure 𝕜 G X (V f) x + R (injectivePure 𝕜 F X f x)) :
    epsilonScalarOperator hX hfew (Q.comp T) = V.comp U := by
  have hsum : HasSeparableRange 𝕜 (InjectiveTensor 𝕜 E X) (InjectiveTensor 𝕜 G X)
      (R.comp (injectiveTensorMap U) + Q.comp S) := by
    apply HasSeparableRange.add (𝕜 := 𝕜)
      (E := InjectiveTensor 𝕜 E X) (F := InjectiveTensor 𝕜 G X)
    · exact HasSeparableRange.comp_right (𝕜 := 𝕜)
        (E := InjectiveTensor 𝕜 E X) (F := InjectiveTensor 𝕜 F X)
        (G := InjectiveTensor 𝕜 G X) hR (injectiveTensorMap U)
    · exact HasSeparableRange.comp_left (𝕜 := 𝕜)
        (E := InjectiveTensor 𝕜 E X) (F := InjectiveTensor 𝕜 F X)
        (G := InjectiveTensor 𝕜 G X) hS Q
  apply epsilonScalarOperator_of_decomposition hX hfew (Q.comp T) (V.comp U)
    (R.comp (injectiveTensorMap U) + Q.comp S) hsum
  intro e x
  change Q (T (injectivePure 𝕜 E X e x)) = _
  calc
    Q (T (injectivePure 𝕜 E X e x)) = Q (injectivePure 𝕜 F X (U e) x + S (injectivePure 𝕜 E X e x)) := congrArg Q (hT e x)
    _ = Q (injectivePure 𝕜 F X (U e) x) + Q (S (injectivePure 𝕜 E X e x)) := map_add Q _ _
    _ = (injectivePure 𝕜 G X (V (U e)) x + R (injectivePure 𝕜 F X (U e) x)) +
        Q (S (injectivePure 𝕜 E X e x)) := congrArg (· + Q (S (injectivePure 𝕜 E X e x))) (hQ (U e) x)
    _ = _ := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, injectiveTensorMap_pure]
      exact add_assoc _ _ _

theorem epsilonScalarOperator_comp [SeparableSpace E]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X)
    (Q : InjectiveTensor 𝕜 F X →L[𝕜] InjectiveTensor 𝕜 G X) :
    epsilonScalarOperator hX hfew (Q.comp T) =
      (epsilonScalarOperator hX hfew Q).comp (epsilonScalarOperator hX hfew T) := by
  exact epsilonScalarOperator_comp_of_decompositions hX hfew T Q
    (epsilonScalarOperator hX hfew T) (epsilonScalarOperator hX hfew Q)
    (epsilonRemainder hX hfew T) (epsilonRemainder hX hfew Q)
    (epsilonRemainder_separable hX hfew T) (epsilonRemainder_separable hX hfew Q)
    (epsilonRemainder_pure hX hfew T) (epsilonRemainder_pure hX hfew Q)

theorem epsilonScalarOperator_id [CompleteSpace E] [SeparableSpace E]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X) :
    epsilonScalarOperator hX hfew (ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 E X)) =
      ContinuousLinearMap.id 𝕜 E := by
  apply epsilonScalarOperator_of_decomposition (E := E) (F := E) hX hfew
    (ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 E X)) (ContinuousLinearMap.id 𝕜 E)
    (0 : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 E X) hasSeparableRange_zero
  intro e x
  simp

theorem epsilonDecomposition [SeparableSpace E]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) :
    ∃! d : (E →L[𝕜] F) × (InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X),
      HasSeparableRange 𝕜 (InjectiveTensor 𝕜 E X) (InjectiveTensor 𝕜 F X) d.2 ∧
      ∀ e x, T (injectivePure 𝕜 E X e x) =
        injectivePure 𝕜 F X (d.1 e) x + d.2 (injectivePure 𝕜 E X e x) := by
  refine ⟨(epsilonScalarOperator hX hfew T, epsilonRemainder hX hfew T),
    ⟨epsilonRemainder_separable hX hfew T, epsilonRemainder_pure hX hfew T⟩, ?_⟩
  rintro ⟨V, R⟩ ⟨hR, hEq⟩
  have hV := epsilonScalarOperator_of_decomposition hX hfew T V R hR hEq
  apply Prod.ext hV.symm
  apply injectiveTensor_ext
  intro e x
  apply add_left_cancel (a := injectivePure 𝕜 F X (V e) x)
  rw [← hEq, ← hV]
  exact epsilonRemainder_pure hX hfew T e x

end ScalarComposition

section Corollary
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F X : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [SeparableSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

omit [SeparableSpace F] in
theorem corollary_1_2 [CompleteSpace E] : Corollary_1_2 𝕜 E F X := by
  intro hE hF hX hfew
  letI : SeparableSpace E := hE
  letI : SeparableSpace F := hF
  constructor
  · rintro ⟨e⟩
    let T := e.toContinuousLinearMap
    let Q := e.symm.toContinuousLinearMap
    let U := epsilonScalarOperator hX hfew T
    let V := epsilonScalarOperator hX hfew Q
    have hQT : Q.comp T = ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 E X) := by
      apply ContinuousLinearMap.ext
      intro z
      exact e.symm_apply_apply z
    have hTQ : T.comp Q = ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 F X) := by
      apply ContinuousLinearMap.ext
      intro z
      exact e.apply_symm_apply z
    have hVU : V.comp U = ContinuousLinearMap.id 𝕜 E := by
      calc
        V.comp U = epsilonScalarOperator hX hfew (Q.comp T) := (epsilonScalarOperator_comp hX hfew T Q).symm
        _ = epsilonScalarOperator hX hfew (ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 E X)) := congrArg _ hQT
        _ = ContinuousLinearMap.id 𝕜 E := epsilonScalarOperator_id hX hfew
    have hUV : U.comp V = ContinuousLinearMap.id 𝕜 F := by
      calc
        U.comp V = epsilonScalarOperator hX hfew (T.comp Q) := (epsilonScalarOperator_comp hX hfew Q T).symm
        _ = epsilonScalarOperator hX hfew (ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 F X)) := congrArg _ hTQ
        _ = ContinuousLinearMap.id 𝕜 F := epsilonScalarOperator_id hX hfew
    exact ⟨ContinuousLinearEquiv.equivOfInverse' U V hUV hVU⟩
  · rintro ⟨e⟩
    let U := e.toContinuousLinearMap
    let V := e.symm.toContinuousLinearMap
    have hVU : V.comp U = ContinuousLinearMap.id 𝕜 E := by
      apply ContinuousLinearMap.ext
      intro z
      exact e.symm_apply_apply z
    have hUV : U.comp V = ContinuousLinearMap.id 𝕜 F := by
      apply ContinuousLinearMap.ext
      intro z
      exact e.apply_symm_apply z
    have hTVU : (injectiveTensorMap (X := X) V).comp (injectiveTensorMap U) =
        ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 E X) := by
      rw [← injectiveTensorMap_comp, hVU, injectiveTensorMap_id]
    have hTUV : (injectiveTensorMap (X := X) U).comp (injectiveTensorMap V) =
        ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 F X) := by
      rw [← injectiveTensorMap_comp, hUV, injectiveTensorMap_id]
    exact ⟨ContinuousLinearEquiv.equivOfInverse' (injectiveTensorMap U) (injectiveTensorMap V) hTUV hTVU⟩

end Corollary
end JFA
