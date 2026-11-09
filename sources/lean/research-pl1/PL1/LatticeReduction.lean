import PL1.LatticeRenorming
import PL1.PartialMainTheorems

/-! # The structural reduction for Theorem A

This module proves a conditional reduction. `SeparableSchurLatticeRNP` is
explicitly supplied as an argument here and is proved in `PL1.MainTheoremA`
using the actual Schur-lattice atomicity and vector-measure RNP theorems.
-/

noncomputable section
universe u
open TopologicalSpace

namespace PL1

/-- The real Banach-lattice structural assertion used by the reduction. This is a
proposition to prove, not an axiom or an instance. -/
def SeparableSchurLatticeRNP : Prop :=
  ∀ (F : Type u) [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
    [BanachLattice F] [SeparableSpace F],
    HasSchurProperty ℝ F → HasRadonNikodymProperty.{u, 0} F

theorem not_hasEquivalentRealLatticeNorm_of_structural_RNP
    (hstruct : SeparableSchurLatticeRNP.{u})
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SeparableSpace E]
    (hS : HasSchurProperty ℝ E) (hRNP : ¬ HasRadonNikodymProperty.{u, 0} E) :
    ¬ HasEquivalentRealLatticeNorm E := by
  intro h
  apply h.elim_separable
  intro F _ _ _ _ _ e
  exact hRNP ((RNPBridge.hasRadonNikodymProperty_iff_equiv e).mpr
    (hstruct F ((hasSchurProperty_equiv_iff e).mp hS)))

/-- Conditional endpoint with exactly the reviewed full A target.
`PL1.MainTheoremA` discharges the structural RNP hypothesis. -/
theorem theoremA_of_separableSchurLatticeRNP (𝕜 : Type u) [RCLike 𝕜]
    (hstruct : SeparableSchurLatticeRNP.{u}) : TheoremAStatement 𝕜 := by
  let P := Noise.intervalProjection 𝕜 Noise.schurRates
  have hclosed := Noise.intervalProjection_range_isClosed 𝕜 Noise.schurRates
  let : CompleteSpace P.range := hclosed.isComplete.completeSpace_coe
  let : SeparableSpace (Noise.projection 𝕜 Noise.schurRates).range :=
    Noise.projection_range_separableSpace 𝕜 Noise.schurRates
  let e := Noise.intervalProjectionRangeEquiv 𝕜 Noise.schurRates
  let : SeparableSpace P.range := e.surjective.denseRange.separableSpace e.continuous
  refine ⟨P, Noise.intervalProjection_isProjection 𝕜 Noise.schurRates,
    Noise.norm_intervalProjection_le 𝕜 Noise.schurRates, hclosed,
    Noise.intervalProjection_range_infiniteDimensional 𝕜 Noise.schurRates,
    Noise.schur_intervalProjection_isDunfordPettis 𝕜,
    Noise.schur_intervalProjection_range_hasSchurProperty 𝕜,
    Noise.schur_intervalProjection_range_not_RNP 𝕜, ?_⟩
  let := NormedSpace.restrictScalars ℝ 𝕜 P.range
  change ¬ HasEquivalentRealLatticeNorm P.range
  apply not_hasEquivalentRealLatticeNorm_of_structural_RNP hstruct
  · exact (hasSchurProperty_iff_underlyingReal 𝕜 P.range).mp
      (Noise.schur_intervalProjection_range_hasSchurProperty 𝕜)
  · exact Noise.schur_intervalProjection_range_not_RNP 𝕜

end PL1
