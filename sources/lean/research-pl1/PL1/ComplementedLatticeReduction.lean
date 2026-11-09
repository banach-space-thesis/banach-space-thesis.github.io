import PL1.ComplementedLatticeRealTrace
import PL1.LatticeRenorming

/-! # Explicit structural dependencies for the full reviewed Theorem B

The operator and real trace obstructions used below are proved. The three
structural properties defined in this file are arguments to the endpoint;
they are not asserted as theorems or registered as instances.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open MeasureTheory TopologicalSpace Topology

namespace PL1.ComplementedLattice

open PL1.EnfloStarbird

/-- An actual isomorphic real L1 model, including its measure space. -/
def HasRealL1Model (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ (Ω : Type u) (m : MeasurableSpace Ω) (μ : @Measure Ω m),
    Nonempty (E ≃L[ℝ] Lp ℝ 1 μ)

/-- The complemented-L1 lattice classification, for the actual ambient L1
space viewed over the reals. For complex scalars this includes the usual
identification of complex L1, with scalars restricted, with a real L1 space. -/
def ComplementedL1LatticeClassification (K : Type u) [RCLike K] : Prop :=
  ∀ (F : Type u) [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
    [BanachLattice F] [SeparableSpace F],
    Nonempty (ComplementedCopy ℝ F (IntervalL1 K)) → HasRealL1Model F

/-- The separable L1 classification consequence actually needed here. -/
def SeparableRealL1Dichotomy : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SeparableSpace E], HasRealL1Model E →
      HasSchurProperty ℝ E ∨ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) E

/-- The real Enflo–Starbird extraction step, restricted to complemented ambient
subspaces as needed by this construction. A proved scalar-to-real copy bridge
below also makes this sufficient to exclude scalar L1 copies. -/
def L1CopyExtraction (K : Type u) [RCLike K] : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SeparableSpace E],
    Nonempty (ComplementedCopy ℝ E (IntervalL1 K)) →
    ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) E →
      Nonempty (ComplementedCopy ℝ (IntervalL1 ℝ) E)

variable {K : Type u} [RCLike K]

/-- A scalar interval L1 copy contains a real interval L1 copy after restricting
scalars. Closedness and the bounded inverse are preserved explicitly. -/
theorem scalar_L1_copy_contains_real_L1 {E : Type u} [NormedAddCommGroup E]
    [NormedSpace K E] [NormedSpace ℝ E] [IsScalarTower ℝ K E] [CompleteSpace E]
    (h : ContainsIsomorphicCopy K (IntervalL1 K) E) :
    ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) E := by
  obtain ⟨V, hV, ⟨e⟩⟩ := h
  let J : IntervalL1 ℝ →L[ℝ] E := (V.subtypeL.restrictScalars ℝ).comp
    ((e.toContinuousLinearMap.restrictScalars ℝ).comp (intervalOfReal K))
  have ho : IsClosedEmbedding (intervalOfReal K) :=
    (show Function.LeftInverse (intervalRe K) (intervalOfReal K) from intervalRe_ofReal K).isClosedEmbedding
      (intervalRe K).continuous (intervalOfReal K).continuous
  have hJ : IsClosedEmbedding J :=
    (V.isClosedEmbedding_subtypeL hV).comp (e.toHomeomorph.isClosedEmbedding.comp ho)
  exact ⟨J.range, hJ.isClosed_range, ⟨J.equivRange hJ.injective hJ.isClosed_range⟩⟩

/-- Identity on vectors, with the natural compatible real action on the source
and the explicitly restricted action used in the reviewed target on the target. -/
def naturalToUnderlyingReal (E : Type u) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedSpace ℝ E] [IsScalarTower ℝ K E] : E ≃L[ℝ] UnderlyingReal K E where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun c x => by
    change c • x = algebraMap ℝ K c • x
    exact (IsScalarTower.algebraMap_smul K c x).symm
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

def projectionRangeCopy (Q : IntervalL1 K →L[K] IntervalL1 K) (hQ : IsProjection Q) :
    ComplementedCopy K Q.range (IntervalL1 K) where
  embedding := Q.range.subtypeL
  retraction := Q.rangeRestrict
  left_inv := fun x => Subtype.ext (hQ.apply_range x)

def projectionRangeCopyReal (Q : IntervalL1 K →L[K] IntervalL1 K) (hQ : IsProjection Q) :
    ComplementedCopy ℝ Q.range (IntervalL1 K) := by
  exact ⟨Q.range.subtypeL.restrictScalars ℝ, Q.rangeRestrict.restrictScalars ℝ,
    fun x => Subtype.ext (hQ.apply_range x)⟩

def complementedCopyTransport {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (C : ComplementedCopy ℝ E G) (e : E ≃L[ℝ] F) : ComplementedCopy ℝ F G where
  embedding := C.embedding.comp e.symm.toContinuousLinearMap
  retraction := e.toContinuousLinearMap.comp C.retraction
  left_inv := fun x => (congrArg e (C.left_inv (e.symm x))).trans (e.apply_symm_apply x)

/-- The actual scalar projection range contains no complemented scalar interval L1. -/
theorem constant_range_no_complemented_scalar_L1 :
    ¬ Nonempty (ComplementedCopy K (IntervalL1 K)
      (Noise.intervalProjection K Noise.constantRates).range) := by
  rw [← identityFactorsThrough_iff_complementedCopy_range _
    (Noise.intervalProjection_isProjection K Noise.constantRates)]
  rintro ⟨A, B, h⟩
  exact Noise.constant_intervalProjection_not_factors_identity K A B h

/-- The stronger real obstruction follows from real vanishing trace, including
when the projection and its range were originally constructed over ℂ. -/
theorem constant_range_no_complemented_real_L1 :
    ¬ Nonempty (ComplementedCopy ℝ (IntervalL1 ℝ)
      (Noise.intervalProjection K Noise.constantRates).range) := by
  let Q := Noise.intervalProjection K Noise.constantRates
  rintro ⟨C⟩
  let A := C.retraction.comp (Q.rangeRestrict.restrictScalars ℝ)
  let B := (Q.range.subtypeL.restrictScalars ℝ).comp C.embedding
  apply (constant_intervalProjection_real_hasVanishingDyadicTrace K).not_factors_identity A B
  ext1 f
  change C.retraction ⟨Q (Q (C.embedding f)), _⟩ = f
  have hq := Noise.intervalProjection_isProjection K Noise.constantRates
  have hx : (⟨Q (Q (C.embedding f)), by exact ⟨Q (C.embedding f), rfl⟩⟩ : Q.range) =
      C.embedding f := by
    apply Subtype.ext
    exact (DFunLike.congr_fun hq (C.embedding f : IntervalL1 K)).trans
      (hq.apply_range (C.embedding f))
  rw [hx]
  exact C.left_inv f

/-- Precisely the reviewed full B target, conditional on the displayed
classification, dichotomy, and arbitrary-copy extraction properties. -/
theorem theoremB_of_structural_properties (K : Type u) [RCLike K]
    (hclass : ComplementedL1LatticeClassification K)
    (hdich : SeparableRealL1Dichotomy.{u}) (hextract : L1CopyExtraction K) :
    TheoremBStatement K := by
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
  refine ⟨Q, hQ, Noise.norm_intervalProjection_le K Noise.constantRates, hclosed,
    Noise.intervalProjection_range_infiniteDimensional K Noise.constantRates,
    Noise.constant_intervalProjection_range_contains_ell2 K, ?_,
    Noise.constant_intervalProjection_range_not_schur K, ?_⟩
  · intro hcopy
    exact constant_range_no_complemented_real_L1
      (hextract Q.range ⟨projectionRangeCopyReal Q hQ⟩
        (scalar_L1_copy_contains_real_L1 hcopy))
  ·
    intro hlat
    apply hlat.elim_separable
    intro F _ _ _ _ _ eF
    let eFn : Q.range ≃L[ℝ] F := (naturalToUnderlyingReal (K := K) Q.range).trans eF
    have hCF : Nonempty (ComplementedCopy ℝ F (IntervalL1 K)) :=
      ⟨complementedCopyTransport (projectionRangeCopyReal Q hQ) eFn⟩
    obtain hs | hc := hdich F (hclass F hCF)
    · exact Noise.constant_intervalProjection_range_not_schur K
        ((hasSchurProperty_iff_real (𝕜 := K) (E := Q.range)).mpr
          ((hasSchurProperty_equiv_iff eFn).mpr hs))
    · have hcQ := hc.map eFn.symm
      exact constant_range_no_complemented_real_L1
        (hextract Q.range ⟨projectionRangeCopyReal Q hQ⟩ hcQ)

#print axioms constant_range_no_complemented_real_L1
#print axioms theoremB_of_structural_properties

end PL1.ComplementedLattice
