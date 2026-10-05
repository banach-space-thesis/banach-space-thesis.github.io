import Posets.SzlenkOrdinalStrictInclusions
import Posets.OrdinalIdealTransportOmega
import Mathlib.Tactic.FinCases

/-! The four-ideal part of Proposition 3.4 reduced to the genuine primary
factorisation theorem and Alspach's surjective non-preserving operator. -/

noncomputable section
open Set ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def fourNontrivialIdealsOfStrictChain {A : Type*} [NormedAddCommGroup A]
    [NormedSpace 𝕜 A] [Mul A] (I₀ I₁ I₂ I₃ : Set A)
    (h₀ : IsClosedIdeal 𝕜 I₀) (h₁ : IsClosedIdeal 𝕜 I₁)
    (h₂ : IsClosedIdeal 𝕜 I₂) (h₃ : IsClosedIdeal 𝕜 I₃)
    (hzero : I₀ ≠ {0}) (htop : I₃ ≠ univ)
    (h₀₁ : I₀ ⊂ I₁) (h₁₂ : I₁ ⊂ I₂) (h₂₃ : I₂ ⊂ I₃) :
    Fin 4 ↪ NontrivialClosedIdeals 𝕜 A := by
  let I : Fin 4 → Set A := ![I₀, I₁, I₂, I₃]
  have hI : StrictMono I := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact h₀₁
    · exact h₁₂
    · exact h₂₃
  have hclosed (i : Fin 4) : IsClosedIdeal 𝕜 (I i) := by
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
  refine ⟨fun i => ⟨I i, hclosed i, ?_, ?_⟩, ?_⟩
  · intro he
    apply hzero
    apply Set.Subset.antisymm
    · have hh : I₀ ⊆ I i := hI.monotone (Fin.zero_le i)
      rwa [he] at hh
    · rintro x rfl
      exact h₀.2.1
  · intro he
    apply htop
    apply Set.eq_univ_of_univ_subset
    have hh : I i ⊆ I₃ := hI.monotone (Fin.le_last i)
    rwa [he] at hh
  · intro i j he
    exact hI.injective (congrArg Subtype.val he)

theorem continuousMap_compactOperators_ne_zero (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] :
    {T : C(K, 𝕜) →L[𝕜] C(K, 𝕜) | IsCompactOperator T} ≠ {0} := by
  let t : K := Classical.choice inferInstance
  let P : C(K, 𝕜) →L[𝕜] C(K, 𝕜) := (ContinuousMap.evalCLM 𝕜 t).smulRight 1
  have hP : IsCompactOperator P := JLMS.isCompactOperator_smulRight _ _
  intro he
  have hz : P = 0 := mem_singleton_iff.mp (he ▸ hP)
  have hh := congrArg (fun T : C(K, 𝕜) →L[𝕜] C(K, 𝕜) => T 1 t) hz
  simpa [P] using hh

theorem ordinalOmegaOmegaSq_four_ideals_of_counterexample
    (hpfp : HasPFP 𝕜 (OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0})))))
    (T : OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) →L[𝕜]
      OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))))
    (hT : Function.Surjective T)
    (hTn : DoesNotFactorIdentity 𝕜 T (OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0})))) ) :
    Nonempty (Fin 4 ↪ NontrivialClosedIdeals 𝕜
      (OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))) →L[𝕜]
        OrdinalSpace 𝕜 (ω ^ (ω ^ (2 : Ordinal.{0}))))) := by
  letI : Nonempty (OrdinalInterval (ω ^ (ω ^ (2 : Ordinal.{0})))) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have hM := (uniqueMaximal_of_hasPFP hpfp).1
  have hs := ordinalOmegaOmegaSq_first_strict_inclusions (𝕜 := 𝕜)
  have ht := szlenk_two_ssubset_nonfactorization_of_surjective
    (ordinalOmegaOmegaSq_not_szlenkBound_omegaSq 𝕜) T hT hTn
  exact ⟨fourNontrivialIdealsOfStrictChain _ _ _ _ JFA.compactOperators_closedIdeal
    isClosedIdeal_szlenk_one isClosedIdeal_szlenk_two hM.1
    (continuousMap_compactOperators_ne_zero _) hM.2.1 hs.1 hs.2 ht⟩

end Posets
