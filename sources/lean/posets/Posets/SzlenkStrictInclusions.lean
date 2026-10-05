import Posets.SzlenkCompact
import Posets.SzlenkNonfactorization
import Posets.SzlenkIdealSurjective
import Posets.ComplementedIdealEmbedding

/-! Concrete projection and surjection witnesses for the strict inclusions
in Proposition 3.4. The required space-specific upper bounds remain explicit. -/

noncomputable section
open Set
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem compact_ssubset_szlenk_one_of_retract
    (i : F →L[𝕜] E) (p : E →L[𝕜] F) (hp : p.comp i = ContinuousLinearMap.id 𝕜 F)
    (hF : OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 F) (ω : Ordinal.{0}))
    (hFn : ¬ IsCompactOperator (ContinuousLinearMap.id 𝕜 F)) :
    {T : E →L[𝕜] E | IsCompactOperator T} ⊂ SzlenkOperatorClass (1 : Ordinal.{0}) := by
  refine ssubset_iff_subset_ne.mpr ⟨compact_subset_szlenk_one, ?_⟩
  intro he
  let P := i.comp ((ContinuousLinearMap.id 𝕜 F).comp p)
  have hP : P ∈ SzlenkOperatorClass (1 : Ordinal.{0}) := by
    simpa only [SzlenkOperatorClass, mem_setOf_eq, Ordinal.opow_one] using hF.comp p i
  have hPc : IsCompactOperator P := by
    have hm : P ∈ {T : E →L[𝕜] E | IsCompactOperator T} := he.symm ▸ hP
    exact hm
  have hc := (hPc.comp_clm i).clm_comp p
  change IsCompactOperator (p.comp (P.comp i)) at hc
  rw [compression_lift_eq i p hp] at hc
  exact hFn hc

theorem szlenk_one_ssubset_two_of_retract
    (i : F →L[𝕜] E) (p : E →L[𝕜] F) (hp : p.comp i = ContinuousLinearMap.id 𝕜 F)
    (hF : OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 F) (ω ^ (2 : Ordinal.{0})))
    (hFn : ¬ OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 F) (ω : Ordinal.{0})) :
    SzlenkOperatorClass (𝕜 := 𝕜) (E := E) (F := E) (1 : Ordinal.{0}) ⊂
      SzlenkOperatorClass (2 : Ordinal.{0}) := by
  refine ssubset_iff_subset_ne.mpr ⟨szlenk_one_subset_two, ?_⟩
  intro he
  let P := i.comp ((ContinuousLinearMap.id 𝕜 F).comp p)
  have hP : P ∈ SzlenkOperatorClass (2 : Ordinal.{0}) := hF.comp p i
  have hPone : OperatorSzlenkBound P (ω : Ordinal.{0}) := by
    have hm := he.symm ▸ hP
    simpa only [SzlenkOperatorClass, mem_setOf_eq, Ordinal.opow_one] using hm
  have hf := hPone.comp i p
  rw [compression_lift_eq i p hp] at hf
  exact hFn hf

theorem szlenk_two_ssubset_nonfactorization_of_surjective [CompleteSpace E]
    (hE : ¬ OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 E) (ω ^ (2 : Ordinal.{0})))
    (T : E →L[𝕜] E) (hT : Function.Surjective T) (hTn : DoesNotFactorIdentity 𝕜 T E) :
    SzlenkOperatorClass (𝕜 := 𝕜) (E := E) (F := E) (2 : Ordinal.{0}) ⊂
      {S | DoesNotFactorIdentity 𝕜 S E} := by
  refine ssubset_iff_subset_ne.mpr ⟨fun S hS => hS.doesNotFactorIdentity hE, ?_⟩
  intro he
  have hm : T ∈ SzlenkOperatorClass (2 : Ordinal.{0}) := he.symm ▸ hTn
  exact hE ((operatorSzlenkBound_surjective_iff T hT _).mp hm)

end Posets
