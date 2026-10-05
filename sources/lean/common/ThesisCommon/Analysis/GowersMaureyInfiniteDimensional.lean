import ThesisCommon.Analysis.GowersMaureyNamedSpace
import ThesisCommon.Analysis.GowersMaureyOperatorTargets
import ThesisCommon.Analysis.PrimaryDirectSum
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Infinite dimension of the actual Gowers--Maurey completion, and the
general implication from primeness to primariness for an infinite-dimensional
normed space. Primeness of the named example is still a separate obligation. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem IsPrimeBanachSpace.isPrimary (h : IsPrimeBanachSpace 𝕜 X)
    (hX : ¬ FiniteDimensional 𝕜 X) : IsPrimary 𝕜 X := by
  intro P hP
  by_cases hfin : FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)
  · apply Or.inr
    apply h _ (complementary_projection hP)
    intro hcomp
    letI := hfin
    letI := hcomp
    exact hX (FiniteDimensional.of_injective
      (projectionRangeComplementEquiv P hP).toLinearMap
      (projectionRangeComplementEquiv P hP).injective)
  · exact Or.inl (h P hP hfin)

theorem GowersMaurey.shiftSpace_infiniteDimensional (D : GowersMaurey.ConstructionData 𝕜) :
    ¬ FiniteDimensional 𝕜 (GowersMaurey.ShiftSpace D) := by
  intro hfin
  letI := hfin
  haveI : FiniteDimensional 𝕜 (GowersMaurey.PreSpace D) :=
    FiniteDimensional.of_injective (GowersMaurey.denseEmbedding D).toLinearMap
      (GowersMaurey.denseEmbedding D).injective
  haveI : FiniteDimensional 𝕜 (ℕ →₀ 𝕜) :=
    inferInstanceAs (FiniteDimensional 𝕜 (GowersMaurey.PreSpace D))
  have hc := (Finsupp.linearIndependent_single_one 𝕜 ℕ).lt_aleph0_of_finiteDimensional
  simp only [Cardinal.mk_nat, lt_self_iff_false] at hc

theorem shiftGowersMaureySpace_infiniteDimensional (𝕜 : Type*) [RCLike 𝕜] :
    ¬ FiniteDimensional 𝕜 (ShiftGowersMaureySpace 𝕜) :=
  GowersMaurey.shiftSpace_infiniteDimensional (GowersMaurey.chosenConstructionData 𝕜)

theorem shiftGowersMaureySpace_primary_of_prime
    (h : IsPrimeBanachSpace 𝕜 (ShiftGowersMaureySpace 𝕜)) :
    IsPrimary 𝕜 (ShiftGowersMaureySpace 𝕜) :=
  h.isPrimary (shiftGowersMaureySpace_infiniteDimensional 𝕜)

end ThesisCommon
