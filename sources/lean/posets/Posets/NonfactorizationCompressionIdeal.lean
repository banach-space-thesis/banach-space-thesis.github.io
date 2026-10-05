import Posets.ComplementedIdealEmbedding
import Posets.OrdinalIdealTransportOmega

/-! The observation preceding Proposition 3.4: whenever the nonfactorisation
class on Y is a closed ideal, its relative version on every X is a closed ideal.
All factorisations here are literal compositions of bounded linear maps. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} {E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem DoesNotFactorIdentity.compression {T : E →L[𝕜] E}
    (h : DoesNotFactorIdentity 𝕜 T F) (A : F →L[𝕜] E) (B : E →L[𝕜] F) :
    DoesNotFactorIdentity 𝕜 (B.comp (T.comp A)) F := by
  rintro ⟨U, V, hUV⟩
  apply h
  refine ⟨A.comp U, V.comp B, ?_⟩
  simpa only [ContinuousLinearMap.comp_assoc] using hUV

theorem nonfactorization_compression_iff (T : E →L[𝕜] E) :
    DoesNotFactorIdentity 𝕜 T F ↔
      ∀ A : F →L[𝕜] E, ∀ B : E →L[𝕜] F, DoesNotFactorIdentity 𝕜 (B.comp (T.comp A)) F := by
  refine ⟨fun h A B => h.compression A B, ?_⟩
  intro h
  rintro ⟨A, B, hAB⟩
  have hh := h A B
  rw [hAB] at hh
  exact hh ⟨ContinuousLinearMap.id 𝕜 F, ContinuousLinearMap.id 𝕜 F, by simp⟩

theorem isClosedIdeal_nonfactorization_relative
    (hF : IsClosedIdeal 𝕜 {T : F →L[𝕜] F | DoesNotFactorIdentity 𝕜 T F}) :
    IsClosedIdeal 𝕜 {T : E →L[𝕜] E | DoesNotFactorIdentity 𝕜 T F} := by
  let J : ClosedIdeal 𝕜 (F →L[𝕜] F) := ⟨_, hF⟩
  have he : {T : E →L[𝕜] E | DoesNotFactorIdentity 𝕜 T F} =
      (compressionIdeal (E := E) J).val := by
    ext T
    exact nonfactorization_compression_iff T
  rw [he]
  exact (compressionIdeal J).property

theorem isClosedIdeal_nonfactorization_of_hasPFP [CompleteSpace F] [Nontrivial F]
    (h : HasPFP 𝕜 F) :
    IsClosedIdeal 𝕜 {T : E →L[𝕜] E | DoesNotFactorIdentity 𝕜 T F} :=
  isClosedIdeal_nonfactorization_relative (uniqueMaximal_of_hasPFP h).1.1

end Posets
