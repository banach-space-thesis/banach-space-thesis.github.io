import PL1.ComplementedLatticeReduction

/-! # A concrete real interval ambient space for the scalar construction

The real and imaginary parts embed scalar L1 into the first two coordinates
of a real L1 sum. The existing probability sampler and averaging retraction
then place that sum complementably in real interval L1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal

namespace PL1.ComplementedLattice

open EnfloStarbird
attribute [local instance] DyadicTrace.intervalMeasure_probability

variable (K : Type*) [RCLike K]

def intervalIm : IntervalL1 K →L[ℝ] IntervalL1 ℝ :=
  (@RCLike.imCLM K _).compLpL 1 intervalMeasure

theorem coeFn_intervalIm (f : IntervalL1 K) :
    intervalIm K f =ᵐ[intervalMeasure] fun x => RCLike.im (f x) :=
  (@RCLike.imCLM K _).coeFn_compLpL f

theorem interval_re_add_im (f : IntervalL1 K) :
    intervalOfReal K (intervalRe K f) + (RCLike.I : K) • intervalOfReal K (intervalIm K f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (intervalOfReal K (intervalRe K f))
      ((RCLike.I : K) • intervalOfReal K (intervalIm K f)),
    Lp.coeFn_smul (RCLike.I : K) (intervalOfReal K (intervalIm K f)),
    coeFn_intervalOfReal K (intervalRe K f), coeFn_intervalOfReal K (intervalIm K f),
    coeFn_intervalRe K f, coeFn_intervalIm K f] with x ha hs hor hoi hr hi
  rw [ha]
  change intervalOfReal K (intervalRe K f) x +
    ((RCLike.I : K) • intervalOfReal K (intervalIm K f)) x = f x
  rw [hs, hor]
  change (intervalRe K f x : K) + (RCLike.I : K) * intervalOfReal K (intervalIm K f) x = _
  rw [hoi, hr, hi, mul_comm RCLike.I, RCLike.re_add_im]

def realCoordinateEmbedding : IntervalL1 K →L[ℝ] L1Sum (IntervalL1 ℝ) :=
  (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => IntervalL1 ℝ) 1 0).comp (intervalRe K) +
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => IntervalL1 ℝ) 1 1).comp (intervalIm K)

def realCoordinateRetraction : L1Sum (IntervalL1 ℝ) →L[ℝ] IntervalL1 K :=
  (intervalOfReal K).comp (lp.evalCLM ℝ (fun _ : ℕ => IntervalL1 ℝ) 1 0) +
    (RCLike.I : K) • (intervalOfReal K).comp (lp.evalCLM ℝ (fun _ : ℕ => IntervalL1 ℝ) 1 1)

theorem realCoordinateRetraction_embedding (f : IntervalL1 K) :
    realCoordinateRetraction K (realCoordinateEmbedding K f) = f := by
  simpa [realCoordinateRetraction, realCoordinateEmbedding, lp.evalCLM, lp.evalₗ,
    lp.single_apply] using interval_re_add_im K f

def realCoordinateCopy : ComplementedCopy ℝ (IntervalL1 K) (L1Sum (IntervalL1 ℝ)) :=
  ⟨realCoordinateEmbedding K, realCoordinateRetraction K, realCoordinateRetraction_embedding K⟩

def realSumIntervalEmbedding : L1Sum (IntervalL1 ℝ) →L[ℝ] IntervalL1 ℝ :=
  (IntervalSubtype.equiv ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((IntervalRetraction.pullback (IntervalModel.probabilityMeasure intervalMeasure)).toContinuousLinearMap.comp
      (IntervalModel.sumProbabilityEquiv (𝕜 := ℝ) intervalMeasure).toContinuousLinearEquiv.toContinuousLinearMap)

def realSumIntervalRetraction : IntervalL1 ℝ →L[ℝ] L1Sum (IntervalL1 ℝ) :=
  (IntervalModel.sumProbabilityEquiv (𝕜 := ℝ) intervalMeasure).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((IntervalRetraction.retraction (IntervalModel.probabilityMeasure intervalMeasure)).comp
      (IntervalSubtype.equiv ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem realSumIntervalRetraction_embedding (f : L1Sum (IntervalL1 ℝ)) :
    realSumIntervalRetraction (realSumIntervalEmbedding f) = f := by
  simp [realSumIntervalRetraction, realSumIntervalEmbedding]

def realSumIntervalCopy : ComplementedCopy ℝ (L1Sum (IntervalL1 ℝ)) (IntervalL1 ℝ) :=
  ⟨realSumIntervalEmbedding, realSumIntervalRetraction, realSumIntervalRetraction_embedding⟩

def complementedCopyComp {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : ComplementedCopy ℝ D E) (B : ComplementedCopy ℝ E F) : ComplementedCopy ℝ D F where
  embedding := B.embedding.comp C.embedding
  retraction := C.retraction.comp B.retraction
  left_inv := fun x => (congrArg C.retraction (B.left_inv (C.embedding x))).trans (C.left_inv x)

/-- Every real or complex interval L1 in this construction embeds complementably
in the actual real interval L1, using its natural compatible real scalar action. -/
def scalarIntervalRealCopy : ComplementedCopy ℝ (IntervalL1 K) (IntervalL1 ℝ) :=
  complementedCopyComp (realCoordinateCopy K) realSumIntervalCopy

/-- The same conclusion with the explicit restricted scalar convention. -/
def underlyingIntervalRealCopy :
    ComplementedCopy ℝ (UnderlyingReal K (IntervalL1 K)) (IntervalL1 ℝ) :=
  complementedCopyTransport (scalarIntervalRealCopy K) (naturalToUnderlyingReal (K := K) (IntervalL1 K))

#print axioms scalarIntervalRealCopy

/-- Only the ordinary real complemented-L1 classification is needed, even for
the complex projection. The reduction uses the actual ambient maps above. -/
theorem classification_of_real (K : Type) [RCLike K]
    (h : ComplementedL1LatticeClassification ℝ) : ComplementedL1LatticeClassification K := by
  intro F _ _ _ _ _ hC
  obtain ⟨C⟩ := hC
  exact h F ⟨complementedCopyComp C (scalarIntervalRealCopy K)⟩

/-- Likewise only real arbitrary-copy extraction in real interval L1 is needed. -/
theorem extraction_of_real (K : Type) [RCLike K]
    (h : L1CopyExtraction ℝ) : L1CopyExtraction K := by
  intro E _ _ _ _ hC hc
  obtain ⟨C⟩ := hC
  exact h E ⟨complementedCopyComp C (scalarIntervalRealCopy K)⟩ hc

/-- The full reviewed scalar target follows from three standard real structural
inputs; all complex/underlying-real and actual-operator bridges are proved. -/
theorem theoremB_of_real_structural_properties (K : Type) [RCLike K]
    (hclass : ComplementedL1LatticeClassification ℝ)
    (hdich : SeparableRealL1Dichotomy.{0}) (hextract : L1CopyExtraction ℝ) :
    TheoremBStatement K :=
  theoremB_of_structural_properties K (classification_of_real K hclass) hdich
    (extraction_of_real K hextract)

theorem theoremB_real_and_complex_of_real_structural_properties
    (hclass : ComplementedL1LatticeClassification ℝ)
    (hdich : SeparableRealL1Dichotomy.{0}) (hextract : L1CopyExtraction ℝ) :
    TheoremBRealStatement ∧ TheoremBComplexStrongStatement :=
  ⟨theoremB_of_real_structural_properties ℝ hclass hdich hextract,
    theoremB_of_real_structural_properties ℂ hclass hdich hextract⟩

#print axioms theoremB_real_and_complex_of_real_structural_properties

end PL1.ComplementedLattice
