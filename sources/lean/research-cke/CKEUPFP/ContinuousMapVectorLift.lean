import CKEUPFP.VectorFiniteRank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Lifting scalar operators to vector-valued continuous functions

A scalar operator is first applied to finite sums of scalar functions times
fixed vectors. Hahn--Banach bounds its norm by the original operator norm,
so the definition respects every representation of a finite-rank function.
Density and completeness then extend it to all continuous vector-valued
functions. In particular, scalar isomorphisms lift to arbitrary Banach ranges.
-/

noncomputable section

namespace CKEUPFP

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K L : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace L] [CompactSpace L]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Interpret a finitely supported collection of scalar-vector generators. -/
def finiteRankTotal : ((C(K, 𝕜) × E) →₀ 𝕜) →ₗ[𝕜] C(K, E) :=
  Finsupp.linearCombination 𝕜 (fun p => scalarVector 𝕜 K E p.1 p.2)

omit [CompactSpace K] in
theorem finiteRankTotal_range :
    LinearMap.range (finiteRankTotal (𝕜 := 𝕜) (K := K) (E := E)) =
      VectorFiniteRank 𝕜 K E := by
  rw [finiteRankTotal, Finsupp.range_linearCombination, VectorFiniteRank]
  congr 1
  ext f
  constructor
  · rintro ⟨⟨g, x⟩, rfl⟩
    exact ⟨g, x, fun _ => rfl⟩
  · rintro ⟨g, x, h⟩
    exact ⟨(g, x), ContinuousMap.ext (fun t => (h t).symm)⟩

/-- Apply a scalar operator to each generator's scalar component. -/
def vectorLiftTotal (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜)) :
    ((C(K, 𝕜) × E) →₀ 𝕜) →ₗ[𝕜] C(L, E) :=
  Finsupp.linearCombination 𝕜 (fun p => scalarVector 𝕜 L E (A p.1) p.2)

omit [CompactSpace K] in
theorem dual_comp_scalarVector (ℓ : StrongDual 𝕜 E) (g : C(K, 𝕜)) (x : E) :
    ℓ.compLeftContinuous 𝕜 K (scalarVector 𝕜 K E g x) = (ℓ x) • g := by
  ext k
  simp [scalarVector, mul_comm]

omit [CompactSpace K] [CompactSpace L] in
theorem vectorLiftTotal_dual (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜))
    (r : (C(K, 𝕜) × E) →₀ 𝕜) (ℓ : StrongDual 𝕜 E) :
    ℓ.compLeftContinuous 𝕜 L (vectorLiftTotal A r) =
      A (ℓ.compLeftContinuous 𝕜 K (finiteRankTotal r)) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, hr, hs]
  | single p c =>
    simp only [vectorLiftTotal, finiteRankTotal, Finsupp.linearCombination_single,
      map_smul, dual_comp_scalarVector]

/-- Hahn--Banach controls the lift's norm by the original scalar norm. -/
theorem norm_vectorLiftTotal_le (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜))
    (r : (C(K, 𝕜) × E) →₀ 𝕜) :
    ‖vectorLiftTotal A r‖ ≤ ‖A‖ * ‖finiteRankTotal r‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg _))).2
  intro l
  apply NormedSpace.norm_le_dual_bound 𝕜 _ (mul_nonneg (norm_nonneg A) (norm_nonneg _))
  intro ℓ
  have hpost : ‖ℓ.compLeftContinuous 𝕜 K (finiteRankTotal r)‖ ≤
      ‖finiteRankTotal r‖ * ‖ℓ‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    intro k
    calc
      ‖ℓ (finiteRankTotal r k)‖ ≤ ‖ℓ‖ * ‖finiteRankTotal r k‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * ‖finiteRankTotal r‖ :=
        mul_le_mul_of_nonneg_left ((finiteRankTotal r).norm_coe_le_norm k) (norm_nonneg _)
      _ = ‖finiteRankTotal r‖ * ‖ℓ‖ := mul_comm _ _
  change ‖(ℓ.compLeftContinuous 𝕜 L (vectorLiftTotal A r)) l‖ ≤ _
  rw [vectorLiftTotal_dual]
  calc
    ‖A (ℓ.compLeftContinuous 𝕜 K (finiteRankTotal r)) l‖ ≤
        ‖A (ℓ.compLeftContinuous 𝕜 K (finiteRankTotal r))‖ :=
      ContinuousMap.norm_coe_le_norm _ l
    _ ≤ ‖A‖ * ‖ℓ.compLeftContinuous 𝕜 K (finiteRankTotal r)‖ := A.le_opNorm _
    _ ≤ ‖A‖ * (‖finiteRankTotal r‖ * ‖ℓ‖) :=
      mul_le_mul_of_nonneg_left hpost (norm_nonneg _)
    _ = (‖A‖ * ‖finiteRankTotal r‖) * ‖ℓ‖ := (mul_assoc _ _ _).symm

theorem vectorLiftTotal_eq_of_total_eq (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜))
    {r s : (C(K, 𝕜) × E) →₀ 𝕜} (h : finiteRankTotal r = finiteRankTotal s) :
    vectorLiftTotal A r = vectorLiftTotal A s := by
  apply sub_eq_zero.mp
  apply norm_le_zero_iff.mp
  have hn := norm_vectorLiftTotal_le A (r - s)
  simpa only [map_sub, h, sub_self, norm_zero, mul_zero] using hn

omit [CompactSpace K] in
theorem vectorFiniteRank_representation (g : VectorFiniteRank 𝕜 K E) :
    ∃ r : (C(K, 𝕜) × E) →₀ 𝕜, finiteRankTotal r = g.val := by
  have hg : g.val ∈ LinearMap.range (finiteRankTotal (𝕜 := 𝕜) (K := K) (E := E)) := by
    simpa only [finiteRankTotal_range] using g.property
  exact hg

def vectorFiniteRankLiftValue (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜))
    (g : VectorFiniteRank 𝕜 K E) : C(L, E) :=
  vectorLiftTotal A (vectorFiniteRank_representation g).choose

theorem vectorFiniteRankLiftValue_eq (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜))
    (g : VectorFiniteRank 𝕜 K E) (r : (C(K, 𝕜) × E) →₀ 𝕜)
    (hr : finiteRankTotal r = g.val) : vectorFiniteRankLiftValue A g = vectorLiftTotal A r :=
  vectorLiftTotal_eq_of_total_eq A ((vectorFiniteRank_representation g).choose_spec.trans hr.symm)

def vectorFiniteRankLift (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜)) :
    VectorFiniteRank 𝕜 K E →L[𝕜] C(L, E) :=
  LinearMap.mkContinuous
    { toFun := vectorFiniteRankLiftValue A
      map_add' := by
        intro f g
        obtain ⟨r, hr⟩ := vectorFiniteRank_representation f
        obtain ⟨s, hs⟩ := vectorFiniteRank_representation g
        have hrs : finiteRankTotal (r + s) = (f + g).val := by
          simp only [map_add, hr, hs, Submodule.coe_add]
        rw [vectorFiniteRankLiftValue_eq A (f + g) (r + s) hrs,
          vectorFiniteRankLiftValue_eq A f r hr, vectorFiniteRankLiftValue_eq A g s hs, map_add]
      map_smul' := by
        intro c f
        obtain ⟨r, hr⟩ := vectorFiniteRank_representation f
        have hcr : finiteRankTotal (c • r) = (c • f).val := by
          simp only [map_smul, hr, Submodule.coe_smul]
        rw [vectorFiniteRankLiftValue_eq A (c • f) (c • r) hcr,
          vectorFiniteRankLiftValue_eq A f r hr, map_smul]
        rfl }
    ‖A‖ (fun f => by
      obtain ⟨r, hr⟩ := vectorFiniteRank_representation f
      change ‖vectorFiniteRankLiftValue A f‖ ≤ ‖A‖ * ‖f‖
      rw [vectorFiniteRankLiftValue_eq A f r hr]
      simpa only [hr] using norm_vectorLiftTotal_le A r)

theorem norm_vectorFiniteRankLift_le (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜)) :
    ‖vectorFiniteRankLift (E := E) A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

variable [T2Space K] [CompleteSpace E]

omit [CompleteSpace E] in
theorem vectorFiniteRank_denseRange :
    DenseRange (VectorFiniteRank 𝕜 K E).subtypeL :=
  denseRange_subtype_val.mpr vectorFiniteRank_dense

/-- Apply any scalar operator to continuous functions with a Banach range. -/
def continuousMapVectorLift (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜)) : C(K, E) →L[𝕜] C(L, E) :=
  (vectorFiniteRankLift A).extend (VectorFiniteRank 𝕜 K E).subtypeL
    vectorFiniteRank_denseRange isUniformEmbedding_subtype_val.isUniformInducing

theorem continuousMapVectorLift_apply_finiteRank (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜))
    (f : VectorFiniteRank 𝕜 K E) :
    continuousMapVectorLift A f.val = vectorFiniteRankLift A f := by
  exact ContinuousLinearMap.extend_eq _ _ _ _ f

theorem norm_continuousMapVectorLift_le (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜)) :
    ‖continuousMapVectorLift (E := E) A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro f
  refine (vectorFiniteRank_denseRange (𝕜 := 𝕜) (K := K) (E := E)).induction_on
    (p := fun f => ‖continuousMapVectorLift A f‖ ≤ ‖A‖ * ‖f‖) f ?_ ?_
  · exact isClosed_le (continuousMapVectorLift A).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro g
    change ‖continuousMapVectorLift A g.val‖ ≤ ‖A‖ * ‖g.val‖
    rw [continuousMapVectorLift_apply_finiteRank]
    exact (vectorFiniteRankLift (E := E) A).le_of_opNorm_le
      (norm_vectorFiniteRankLift_le (E := E) A) g

@[simp]
theorem continuousMapVectorLift_scalarVector (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜))
    (g : C(K, 𝕜)) (x : E) :
    continuousMapVectorLift A (scalarVector 𝕜 K E g x) = scalarVector 𝕜 L E (A g) x := by
  classical
  let f : VectorFiniteRank 𝕜 K E := ⟨scalarVector 𝕜 K E g x, scalarVector_mem g x⟩
  let r : (C(K, 𝕜) × E) →₀ 𝕜 := Finsupp.single (g, x) 1
  have hr : finiteRankTotal r = f.val := by
    simp [r, finiteRankTotal, f]
  change continuousMapVectorLift A f.val = _
  rw [continuousMapVectorLift_apply_finiteRank]
  change vectorFiniteRankLiftValue A f = _
  rw [vectorFiniteRankLiftValue_eq A f r hr]
  simp [vectorLiftTotal, r]

theorem continuousMapVectorLift_id :
    continuousMapVectorLift (E := E) (ContinuousLinearMap.id 𝕜 C(K, 𝕜)) =
      ContinuousLinearMap.id 𝕜 C(K, E) := by
  apply ContinuousLinearMap.ext
  intro f
  change continuousMapVectorLift (ContinuousLinearMap.id 𝕜 C(K, 𝕜)) f = f
  refine (vectorFiniteRank_denseRange (𝕜 := 𝕜) (K := K) (E := E)).induction_on
    (p := fun f => continuousMapVectorLift (ContinuousLinearMap.id 𝕜 C(K, 𝕜)) f = f)
    f ?_ ?_
  · exact isClosed_eq (continuousMapVectorLift _).continuous continuous_id
  · intro g
    obtain ⟨r, hr⟩ := vectorFiniteRank_representation g
    change continuousMapVectorLift (ContinuousLinearMap.id 𝕜 C(K, 𝕜)) g.val = g.val
    rw [← hr]
    clear hr
    induction r using Finsupp.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [map_add, hr, hs]
    | single p c =>
      simp only [finiteRankTotal, Finsupp.linearCombination_single, map_smul,
        continuousMapVectorLift_scalarVector, ContinuousLinearMap.id_apply]

theorem continuousMapVectorLift_comp [T2Space L]
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (B : C(L, 𝕜) →L[𝕜] C(M, 𝕜)) (A : C(K, 𝕜) →L[𝕜] C(L, 𝕜)) :
    (continuousMapVectorLift (E := E) B).comp (continuousMapVectorLift A) =
      continuousMapVectorLift (B.comp A) := by
  apply ContinuousLinearMap.ext
  intro f
  change continuousMapVectorLift B (continuousMapVectorLift A f) =
    continuousMapVectorLift (B.comp A) f
  refine (vectorFiniteRank_denseRange (𝕜 := 𝕜) (K := K) (E := E)).induction_on
    (p := fun f => continuousMapVectorLift B (continuousMapVectorLift A f) =
      continuousMapVectorLift (B.comp A) f) f ?_ ?_
  · exact isClosed_eq ((continuousMapVectorLift B).continuous.comp
      (continuousMapVectorLift A).continuous) (continuousMapVectorLift (B.comp A)).continuous
  · intro g
    obtain ⟨r, hr⟩ := vectorFiniteRank_representation g
    change continuousMapVectorLift B (continuousMapVectorLift A g.val) =
      continuousMapVectorLift (B.comp A) g.val
    rw [← hr]
    clear hr
    induction r using Finsupp.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [map_add, hr, hs]
    | single p c =>
      simp only [finiteRankTotal, Finsupp.linearCombination_single, map_smul,
        continuousMapVectorLift_scalarVector, ContinuousLinearMap.comp_apply]

/-- Lift a scalar isomorphism to any Banach-valued continuous function space. -/
def continuousMapVectorEquiv [T2Space L] (e : C(K, 𝕜) ≃L[𝕜] C(L, 𝕜)) :
    C(K, E) ≃L[𝕜] C(L, E) where
  __ := (continuousMapVectorLift e.toContinuousLinearMap).toLinearMap
  invFun := continuousMapVectorLift e.symm.toContinuousLinearMap
  left_inv f := by
    have heq : e.symm.toContinuousLinearMap.comp e.toContinuousLinearMap =
        ContinuousLinearMap.id 𝕜 C(K, 𝕜) := by
      apply ContinuousLinearMap.ext
      intro g
      exact e.symm_apply_apply g
    have h := congrArg (fun F : C(K, E) →L[𝕜] C(K, E) => F f)
      (continuousMapVectorLift_comp e.symm.toContinuousLinearMap e.toContinuousLinearMap)
    simpa only [ContinuousLinearMap.comp_apply, heq, continuousMapVectorLift_id,
      ContinuousLinearMap.id_apply] using h
  right_inv f := by
    have heq : e.toContinuousLinearMap.comp e.symm.toContinuousLinearMap =
        ContinuousLinearMap.id 𝕜 C(L, 𝕜) := by
      apply ContinuousLinearMap.ext
      intro g
      exact e.apply_symm_apply g
    have h := congrArg (fun F : C(L, E) →L[𝕜] C(L, E) => F f)
      (continuousMapVectorLift_comp e.toContinuousLinearMap e.symm.toContinuousLinearMap)
    simpa only [ContinuousLinearMap.comp_apply, heq, continuousMapVectorLift_id,
      ContinuousLinearMap.id_apply] using h
  continuous_toFun := (continuousMapVectorLift e.toContinuousLinearMap).continuous
  continuous_invFun := (continuousMapVectorLift e.symm.toContinuousLinearMap).continuous

end CKEUPFP
