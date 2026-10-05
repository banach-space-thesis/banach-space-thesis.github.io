import PEMS.Definitions
import ThesisCommon.Analysis.OperatorIsometryTransport

/-! Actual factorization constants are preserved by onto linear isometries
of the domain and codomain. Equality follows by transporting the witnesses;
no attainment, nontriviality, or finiteness of a supremum is assumed. -/
noncomputable section
open ThesisCommon Set
namespace PEMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F E' F' Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem factorization_witness_of_operatorTransport
    (a : E ≃ₗᵢ[𝕜] E') (b : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F)
    (U : F' →L[𝕜] Z) (V : Z →L[𝕜] E')
    (h : U.comp ((operatorTransport a b T).comp V) = ContinuousLinearMap.id 𝕜 Z) :
    ∃ (U' : F →L[𝕜] Z) (V' : Z →L[𝕜] E),
      U'.comp (T.comp V') = ContinuousLinearMap.id 𝕜 Z ∧
        ‖U'‖ = ‖U‖ ∧ ‖V'‖ = ‖V‖ := by
  refine ⟨U.comp b.toLinearIsometry.toContinuousLinearMap,
    a.symm.toLinearIsometry.toContinuousLinearMap.comp V, ?_,
    U.opNorm_comp_linearIsometryEquiv b,
    a.symm.toLinearIsometry.norm_toContinuousLinearMap_comp⟩
  apply ContinuousLinearMap.ext
  intro z
  exact DFunLike.congr_fun h z

theorem factorizationSup_operatorTransport
    (a : E ≃ₗᵢ[𝕜] E') (b : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F) :
    factorizationSup Z (operatorTransport a b T) = factorizationSup Z T := by
  unfold factorizationSup
  congr 1
  ext r
  constructor
  · rintro (rfl | ⟨U, V, h, rfl⟩)
    · exact Set.mem_insert 0 _
    · obtain ⟨U', V', h', hU, hV⟩ := factorization_witness_of_operatorTransport a b T U V h
      exact Set.mem_insert_of_mem _ ⟨U', V', h', by rw [hU, hV]⟩
  · rintro (rfl | ⟨U, V, h, rfl⟩)
    · exact Set.mem_insert 0 _
    · have h' : U.comp ((operatorTransport a.symm b.symm (operatorTransport a b T)).comp V) =
          ContinuousLinearMap.id 𝕜 Z := by rwa [operatorTransport_symm]
      obtain ⟨U', V', h'', hU, hV⟩ :=
        factorization_witness_of_operatorTransport a.symm b.symm (operatorTransport a b T) U V h'
      exact Set.mem_insert_of_mem _ ⟨U', V', h'', by rw [hU, hV]⟩

end PEMS
