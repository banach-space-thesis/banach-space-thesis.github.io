import PL1.WeakSchur
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Analysis.Normed.Ring.Units

/-! # The projection and factorization step in the Enflo–Starbird route

This file proves the bounded inverse/projection construction from a quantitative
approximate left inverse. It does not assert the missing Enflo–Starbird
disjoint-tree extraction theorem for arbitrary L1 embeddings.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PL1.EnfloStarbird

variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A complemented copy described by its actual bounded embedding and retraction. -/
structure ComplementedCopy (𝕜 D E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] where
  embedding : D →L[𝕜] E
  retraction : E →L[𝕜] D
  left_inv : Function.LeftInverse retraction embedding

namespace ComplementedCopy

variable (C : ComplementedCopy 𝕜 D E)

def projection : E →L[𝕜] E := C.embedding.comp C.retraction

@[simp] theorem projection_apply (x : E) : C.projection x = C.embedding (C.retraction x) := rfl

theorem isProjection : IsProjection C.projection := by
  ext x
  exact congrArg C.embedding (C.left_inv (C.retraction x))

theorem range_projection : C.projection.range = C.embedding.range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨C.retraction y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨C.embedding y, congrArg C.embedding (C.left_inv y)⟩

theorem closedComplemented_range : C.embedding.range.ClosedComplemented :=
  C.embedding.closedComplemented_range_of_leftInverse C.retraction C.left_inv

def rangeEquiv : D ≃L[𝕜] C.embedding.range :=
  ContinuousLinearEquiv.equivOfInverse C.embedding.rangeRestrict
    (C.retraction.comp C.embedding.range.subtypeL)
    C.left_inv (by
      rintro ⟨x, y, hy⟩
      apply Subtype.ext
      change C.embedding (C.retraction x) = x
      rw [← hy]
      exact congrArg C.embedding (C.left_inv y))

include C in
theorem containsIsomorphicCopy : ContainsIsomorphicCopy 𝕜 D E :=
  ⟨C.embedding.range, C.closedComplemented_range.isClosed, ⟨C.rangeEquiv⟩⟩

theorem norm_projection_le : ‖C.projection‖ ≤ ‖C.embedding‖ * ‖C.retraction‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

end ComplementedCopy

/-- The concrete maps are equivalent to the usual complemented-subspace definition. -/
theorem nonempty_complementedCopy_iff : Nonempty (ComplementedCopy 𝕜 D E) ↔
    ∃ V : Submodule 𝕜 E, V.ClosedComplemented ∧ Nonempty (D ≃L[𝕜] V) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.embedding.range, C.closedComplemented_range, ⟨C.rangeEquiv⟩⟩
  · rintro ⟨V, ⟨P, hP⟩, ⟨e⟩⟩
    exact ⟨⟨V.subtypeL.comp e.toContinuousLinearMap,
      e.symm.toContinuousLinearMap.comp P,
      fun x => (congrArg e.symm (hP (e x))).trans (e.symm_apply_apply x)⟩⟩

variable [CompleteSpace D]

/-- Neumann-series correction of an approximate left inverse. -/
def correctedRetraction (J : D →L[𝕜] E) (R : E →L[𝕜] D)
    (h : ‖1 - R.comp J‖ < 1) : E →L[𝕜] D :=
  ((↑(Units.oneSub (1 - R.comp J) h)⁻¹ : D →L[𝕜] D)).comp R

theorem correctedRetraction_left_inv (J : D →L[𝕜] E) (R : E →L[𝕜] D)
    (h : ‖1 - R.comp J‖ < 1) : Function.LeftInverse (correctedRetraction J R h) J := by
  let U := Units.oneSub (1 - R.comp J) h
  have hU : (↑U : D →L[𝕜] D) = R.comp J := by simp [U]
  have hi : (↑U⁻¹ : D →L[𝕜] D).comp (R.comp J) = ContinuousLinearMap.id 𝕜 D := by
    rw [← hU]
    exact U.inv_val
  intro x
  exact DFunLike.congr_fun hi x

/-- An approximate inverse at distance below one produces a genuine complemented copy. -/
def complementedCopyOfApproximateInverse (J : D →L[𝕜] E) (R : E →L[𝕜] D)
    (h : ‖1 - R.comp J‖ < 1) : ComplementedCopy 𝕜 D E :=
  ⟨J, correctedRetraction J R h, correctedRetraction_left_inv J R h⟩

theorem norm_correctedRetraction_le (J : D →L[𝕜] E) (R : E →L[𝕜] D)
    (h : ‖1 - R.comp J‖ < 1) :
    ‖correctedRetraction J R h‖ ≤ (1 - ‖1 - R.comp J‖)⁻¹ * ‖R‖ := by
  have hu : ‖(↑(Units.oneSub (1 - R.comp J) h)⁻¹ : D →L[𝕜] D)‖ ≤
      (1 - ‖1 - R.comp J‖)⁻¹ := by
    change ‖∑' n : ℕ, (1 - R.comp J) ^ n‖ ≤ _
    have hb := tsum_geometric_le_of_norm_lt_one (1 - R.comp J) h
    have h1 : ‖(1 : D →L[𝕜] D)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    linarith
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hu (norm_nonneg R))

theorem norm_approximateInverse_projection_le (J : D →L[𝕜] E) (R : E →L[𝕜] D)
    (h : ‖1 - R.comp J‖ < 1) :
    ‖(complementedCopyOfApproximateInverse J R h).projection‖ ≤
      ‖J‖ * ((1 - ‖1 - R.comp J‖)⁻¹ * ‖R‖) :=
  (ComplementedCopy.norm_projection_le _).trans
    (mul_le_mul_of_nonneg_left (norm_correctedRetraction_le J R h) (norm_nonneg J))

theorem closedComplemented_range_of_approximateInverse (J : D →L[𝕜] E)
    (R : E →L[𝕜] D) (h : ‖1 - R.comp J‖ < 1) : J.range.ClosedComplemented :=
  (complementedCopyOfApproximateInverse J R h).closedComplemented_range

/-- Exact bounded factorization of the identity through the indicated operator. -/
def IdentityFactorsThrough (Q : E →L[𝕜] E) : Prop :=
  ∃ A : E →L[𝕜] D, ∃ B : D →L[𝕜] E,
    A.comp (Q.comp B) = ContinuousLinearMap.id 𝕜 D

private theorem projection_fixes_range (Q : E →L[𝕜] E) (hQ : IsProjection Q)
    (y : Q.range) : Q (y : E) = y := by
  obtain ⟨z, hz⟩ := y.property
  rw [← hz]
  exact DFunLike.congr_fun hQ z

omit [CompleteSpace D] in
/-- For a projection, identity factorization means exactly a complemented copy in its range. -/
theorem identityFactorsThrough_iff_complementedCopy_range (Q : E →L[𝕜] E)
    (hQ : IsProjection Q) : IdentityFactorsThrough (D := D) Q ↔
      Nonempty (ComplementedCopy 𝕜 D Q.range) := by
  constructor
  · rintro ⟨A, B, h⟩
    exact ⟨⟨Q.rangeRestrict.comp B, A.comp Q.range.subtypeL,
      fun x => DFunLike.congr_fun h x⟩⟩
  · rintro ⟨C⟩
    refine ⟨C.retraction.comp Q.rangeRestrict, Q.range.subtypeL.comp C.embedding, ?_⟩
    ext x
    change C.retraction ⟨Q (Q (C.embedding x)), _⟩ = x
    have hy : (⟨Q (Q (C.embedding x)), by exact ⟨Q (C.embedding x), rfl⟩⟩ : Q.range) =
        C.embedding x := by
      apply Subtype.ext
      exact (congrArg Q (projection_fixes_range Q hQ (C.embedding x))).trans
        (projection_fixes_range Q hQ (C.embedding x))
    rw [hy]
    exact C.left_inv x

omit [CompleteSpace D] in
/-- The no-factorization conclusion rules out every complemented copy in the range. -/
theorem no_complementedCopy_range_of_no_factorization (Q : E →L[𝕜] E)
    (hQ : IsProjection Q) (h : ¬ IdentityFactorsThrough (D := D) Q) :
    ¬ Nonempty (ComplementedCopy 𝕜 D Q.range) :=
  fun hc => h ((identityFactorsThrough_iff_complementedCopy_range Q hQ).mpr hc)

/-- A norm distance below one already implies exact factorization, by correcting the inverse. -/
theorem identityFactorsThrough_of_approximation (Q : E →L[𝕜] E)
    (A : E →L[𝕜] D) (B : D →L[𝕜] E)
    (h : ‖1 - A.comp (Q.comp B)‖ < 1) : IdentityFactorsThrough (D := D) Q := by
  refine ⟨correctedRetraction (Q.comp B) A h, B, ?_⟩
  ext x
  exact correctedRetraction_left_inv (Q.comp B) A h x

/-- In a Banach domain, failure of exact factorization entails the sharp unit-distance barrier. -/
theorem one_le_norm_sub_of_no_factorization (Q : E →L[𝕜] E)
    (h : ¬ IdentityFactorsThrough (D := D) Q)
    (A : E →L[𝕜] D) (B : D →L[𝕜] E) :
    1 ≤ ‖1 - A.comp (Q.comp B)‖ := by
  by_contra hn
  exact h (identityFactorsThrough_of_approximation Q A B (lt_of_not_ge hn))

#print axioms complementedCopyOfApproximateInverse
#print axioms norm_approximateInverse_projection_le
#print axioms nonempty_complementedCopy_iff
#print axioms identityFactorsThrough_iff_complementedCopy_range
#print axioms one_le_norm_sub_of_no_factorization

end PL1.EnfloStarbird
