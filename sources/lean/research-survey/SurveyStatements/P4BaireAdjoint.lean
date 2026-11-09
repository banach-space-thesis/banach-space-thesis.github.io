import SurveyStatements.P4Bidual
import SurveyStatements.P4WeakMetric
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Norm regularity of the adjoint in the weak-star topology

These are the concrete topological ingredients of the source's Baire-one
adjoint argument. No Baire-one characterization is assumed here.
-/

noncomputable section
set_option autoImplicit false

open Set Topology TopologicalSpace

namespace SurveyStatements.P4

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Precomposition by an operator is continuous for the actual weak-star
topologies on both dual spaces. -/
def weakStarAdjoint (T : X →L[𝕜] Y) : WeakDual 𝕜 Y →L[𝕜] WeakDual 𝕜 X where
  toLinearMap := (StrongDual.toWeakDual.toLinearMap.comp
    (banachAdjoint T).toLinearMap).comp WeakDual.toStrongDual.toLinearMap
  cont := by
    apply WeakDual.continuous_of_continuous_eval
    intro x
    exact WeakDual.eval_continuous (T x)

/-- Norm-closed balls under the adjoint have weak-star closed preimages,
including balls with an arbitrary center in the full dual of the domain. -/
theorem adjoint_normBall_preimage_isClosed (T : X →L[𝕜] Y)
    (η : StrongDual 𝕜 X) (r : ℝ) :
    IsClosed {φ : WeakDual 𝕜 Y |
      ‖banachAdjoint T (WeakDual.toStrongDual φ) - η‖ ≤ r} := by
  simpa only [Set.preimage, Metric.mem_closedBall, dist_eq_norm, weakStarAdjoint]
    using (WeakDual.isClosed_closedBall η r).preimage (weakStarAdjoint T).continuous

/-- A weak-star compact set in the dual of a separable normed space is
metrizable. No norm separability of its dual is required. -/
theorem weakStarCompact_metrizable [SeparableSpace Y]
    {K : Set (WeakDual 𝕜 Y)} (hK : IsCompact K) : MetrizableSpace K := by
  classical
  obtain ⟨D, hD, hdense⟩ := exists_countable_dense Y
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Countable D := hD.to_subtype
  let c : K → (D → 𝕜) := fun φ y => φ.val y.val
  have hc : Continuous c := by
    apply continuous_pi
    intro y
    exact (WeakDual.eval_continuous y.val).comp continuous_subtype_val
  have hinj : Function.Injective c := by
    intro φ ψ h
    apply Subtype.ext
    apply DFunLike.ext
    intro y
    have heq : IsClosed {y : Y | φ.val y = ψ.val y} :=
      isClosed_eq φ.val.continuous ψ.val.continuous
    have hDsub : D ⊆ {y : Y | φ.val y = ψ.val y} := by
      intro z hz
      exact congrFun h ⟨z, hz⟩
    exact (closure_minimal hDsub heq) (hdense y)
  exact (hc.isClosedEmbedding hinj).isEmbedding.metrizableSpace

/-- The weak closure of the unit-ball image, viewed as a concrete compact
parameter space when the operator is weakly compact. -/
def weakClosureImage (T : X →L[𝕜] Y) : Set (WeakSpace 𝕜 Y) :=
  closure ((toWeakSpace 𝕜 Y) '' (T '' Metric.closedBall (0 : X) 1))

/-- Restriction of a functional to the actual weak closure of the image. -/
def weakClosureRestriction (T : X →L[𝕜] Y) (φ : StrongDual 𝕜 Y) :
    C(weakClosureImage T, 𝕜) where
  toFun := fun y => φ ((toWeakSpace 𝕜 Y).symm y.val)
  continuous_toFun :=
    (WeakBilin.eval_continuous (topDualPairing 𝕜 Y).flip φ).comp continuous_subtype_val

/-- Restriction to the weak closure has exactly the norm of the adjoint
functional. This is the isometric realization used in the source. -/
theorem weakClosureRestriction_norm (T : X →L[𝕜] Y)
    (hT : IsWeaklyCompactOperator 𝕜 T) (φ : StrongDual 𝕜 Y) :
    letI : CompactSpace (weakClosureImage T) := isCompact_iff_compactSpace.mp hT
    ‖weakClosureRestriction T φ‖ = ‖banachAdjoint T φ‖ := by
  letI : CompactSpace (weakClosureImage T) := isCompact_iff_compactSpace.mp hT
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro y
    let S : Set (WeakSpace 𝕜 Y) :=
      {z | ‖φ ((toWeakSpace 𝕜 Y).symm z)‖ ≤ ‖banachAdjoint T φ‖}
    have hS : IsClosed S :=
      isClosed_le (WeakBilin.eval_continuous (topDualPairing 𝕜 Y).flip φ).norm
        continuous_const
    have hsub : ((toWeakSpace 𝕜 Y) '' (T '' Metric.closedBall (0 : X) 1)) ⊆ S := by
      rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact (banachAdjoint T φ).unit_le_opNorm x (by simpa using hx)
    exact closure_minimal hsub hS y.property
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
    intro x hx
    let y : weakClosureImage T := ⟨toWeakSpace 𝕜 Y (T x),
      subset_closure ⟨T x, ⟨x, by simpa using hx.le, rfl⟩, rfl⟩⟩
    exact (weakClosureRestriction T φ).norm_coe_le_norm y

/-- For a weakly compact operator into a separable space, the entire adjoint
range is norm separable, even if the codomain dual is not norm separable. -/
theorem weaklyCompact_adjoint_range_isSeparable [SeparableSpace Y]
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T) :
    IsSeparable (Set.range (banachAdjoint T)) := by
  classical
  let W := weakClosureImage T
  letI : CompactSpace W := isCompact_iff_compactSpace.mp hT
  letI : MetrizableSpace W := weakCompact_metrizable hT
  letI : SecondCountableTopology W := inferInstance
  let R := Set.range (banachAdjoint T)
  let representative : R → StrongDual 𝕜 Y := fun η => η.property.choose
  have hrep (η : R) : banachAdjoint T (representative η) = η.val :=
    η.property.choose_spec
  let f : R → C(W, 𝕜) := fun η => weakClosureRestriction T (representative η)
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro η ζ
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hsub : f η - f ζ =
        weakClosureRestriction T (representative η - representative ζ) := by
      ext y
      rfl
    rw [hsub, weakClosureRestriction_norm T hT, map_sub, hrep, hrep]
  letI : SeparableSpace R := hf.isEmbedding.separableSpace
  exact IsSeparable.of_subtype _

end SurveyStatements.P4
