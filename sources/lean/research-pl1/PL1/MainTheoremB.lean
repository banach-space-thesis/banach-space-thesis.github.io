import PL1.ALAlternative
import PL1.EnfloNoL1
import PL1.ComplementedLatticeRealAmbient

/-!
# The full reviewed Theorem B

The actual constant-rate projection range contains no interval L1 copy.
If it admitted an equivalent real lattice norm, the complemented-L1 lattice
alternative would make it Schur or yield a real interval L1 copy. Both
possibilities contradict proved properties of this same range.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open TopologicalSpace

namespace PL1
open PL1.ComplementedLattice

/-- Every reviewed clause of B holds for the actual constant-rate projection,
including the stronger underlying-real nonlattice clause for complex scalars. -/
theorem constant_intervalProjection_theoremBSpec (K : Type u) [RCLike K] :
    TheoremBSpec K (Noise.intervalProjection K Noise.constantRates) := by
  let Q := Noise.intervalProjection K Noise.constantRates
  have hQ := Noise.intervalProjection_isProjection K Noise.constantRates
  have hclosed := Noise.intervalProjection_range_isClosed K Noise.constantRates
  let : CompleteSpace Q.range := hclosed.isComplete.completeSpace_coe
  let : SeparableSpace (Noise.projection K Noise.constantRates).range :=
    Noise.projection_range_separableSpace K Noise.constantRates
  let e := Noise.intervalProjectionRangeEquiv K Noise.constantRates
  let : SeparableSpace Q.range := e.surjective.denseRange.separableSpace e.continuous
  let : CompleteSpace (UnderlyingReal K Q.range) := inferInstanceAs (CompleteSpace Q.range)
  let : SeparableSpace (UnderlyingReal K Q.range) := inferInstanceAs (SeparableSpace Q.range)
  refine ⟨hQ, Noise.norm_intervalProjection_le K Noise.constantRates, hclosed,
    Noise.intervalProjection_range_infiniteDimensional K Noise.constantRates,
    Noise.constant_intervalProjection_range_contains_ell2 K, ?_,
    Noise.constant_intervalProjection_range_not_schur K, ?_⟩
  · intro hcopy
    exact Noise.constant_intervalProjection_range_no_real_L1 K
      (scalar_L1_copy_contains_real_L1 hcopy)
  · intro hlat
    apply hlat.elim_separable
    intro F _ _ _ _ _ eF
    let eFn : Q.range ≃L[ℝ] F := (naturalToUnderlyingReal (K := K) Q.range).trans eF
    let CF := complementedCopyTransport (projectionRangeCopyReal Q hQ) eFn
    let CFreal := complementedCopyComp CF (scalarIntervalRealCopy K)
    obtain hs | hc := ALAlternative.schur_or_contains_interval_of_complemented CFreal
    · exact Noise.constant_intervalProjection_range_not_schur K
        ((hasSchurProperty_iff_real (𝕜 := K) (E := Q.range)).mpr
          ((hasSchurProperty_equiv_iff eFn).mpr hs))
    · exact Noise.constant_intervalProjection_range_no_real_L1 K (hc.map eFn.symm)

theorem theoremB (K : Type u) [RCLike K] : TheoremBStatement K :=
  ⟨Noise.intervalProjection K Noise.constantRates, constant_intervalProjection_theoremBSpec K⟩

theorem theoremBReal : TheoremBRealStatement := theoremB ℝ

theorem theoremBComplexStrong : TheoremBComplexStrongStatement := theoremB ℂ

end PL1
