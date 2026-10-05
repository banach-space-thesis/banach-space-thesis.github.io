import ThesisCommon.Analysis.JamesBidualCoordinates
import ThesisCommon.Analysis.JamesBidualConstant
import ThesisCommon.Analysis.QuasiReflexiveDefinitions

/-! The genuine James sequence space is quasi-reflexive of order one for
1 < p < infinity. The map on the actual bidual is the limit of its coordinate
sequence. Its kernel is exactly the canonical image, and the constructed
constant-one bidual functional maps to one. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

local instance jamesQuasiBidualGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))
    (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)
local instance jamesQuasiBidualSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))
    (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)
local instance jamesQuasiBidualQuotient :
    HasQuotient (StrongDual 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p)))
      (Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p)))) :=
  @Submodule.hasQuotient 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p)))
    inferInstance inferInstance inferInstance

def jamesBidualLimitLinear :
    ((JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 where
  toFun := jamesBidualLimit p hp
  map_add' ξ ζ := tendsto_nhds_unique (jamesBidualCoordinate_tendsto p hp (ξ + ζ))
    ((jamesBidualCoordinate_tendsto p hp ξ).add (jamesBidualCoordinate_tendsto p hp ζ))
  map_smul' a ξ := tendsto_nhds_unique (jamesBidualCoordinate_tendsto p hp (a • ξ))
    (tendsto_const_nhds.smul (jamesBidualCoordinate_tendsto p hp ξ))

theorem jamesBidualLimit_canonical (x : JamesSequenceSpace 𝕜 p) :
    jamesBidualLimit p hp (NormedSpace.inclusionInDoubleDual 𝕜 (JamesSequenceSpace 𝕜 p) x) = 0 := by
  have ht := jamesBidualCoordinate_tendsto p hp
    (NormedSpace.inclusionInDoubleDual 𝕜 (JamesSequenceSpace 𝕜 p) x)
  exact tendsto_nhds_unique ht x.tendsto_zero

theorem jamesBidualLimit_constant (hpl : 1 < p.val.toReal) :
    jamesBidualLimit p hp (jamesBidualConstant (𝕜 := 𝕜) p hp hpl) = 1 := by
  have ht := jamesBidualCoordinate_tendsto p hp (jamesBidualConstant (𝕜 := 𝕜) p hp hpl)
  change Tendsto (fun n => jamesBidualConstant (𝕜 := 𝕜) p hp hpl
    (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)) atTop _ at ht
  simp only [jamesBidualConstant_coordinate] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem jamesBidualLimit_ker_eq (hpl : 1 < p.val.toReal) :
    LinearMap.ker (jamesBidualLimitLinear (𝕜 := 𝕜) p hp) = bidualImage 𝕜 (JamesSequenceSpace 𝕜 p) := by
  ext ξ
  change jamesBidualLimit p hp ξ = 0 ↔
    ∃ x, NormedSpace.inclusionInDoubleDual 𝕜 (JamesSequenceSpace 𝕜 p) x = ξ
  constructor
  · intro hξ
    refine ⟨jamesBidualNullPart p hp ξ, ?_⟩
    apply james_bidual_ext_coordinates p hp hpl
    intro n
    change jamesBidualNullPart p hp ξ n = jamesBidualCoordinate p ξ n
    simp only [jamesBidualNullPart_apply, hξ, sub_zero]
  · rintro ⟨x, rfl⟩
    exact jamesBidualLimit_canonical p hp x

theorem jamesBidualLimit_surjective (hpl : 1 < p.val.toReal) :
    Function.Surjective (jamesBidualLimitLinear (𝕜 := 𝕜) p hp) := by
  intro a
  refine ⟨a • jamesBidualConstant (𝕜 := 𝕜) p hp hpl, ?_⟩
  rw [map_smul]
  change a * jamesBidualLimit p hp (jamesBidualConstant (𝕜 := 𝕜) p hp hpl) = a
  rw [jamesBidualLimit_constant p hp hpl, mul_one]

/-- The actual bidual quotient of Jp is linearly isomorphic to the scalar field. -/
def jamesResiduumScalarEquiv (hpl : 1 < p.val.toReal) :
    ResiduumSpace 𝕜 (JamesSequenceSpace 𝕜 p) ≃ₗ[𝕜] 𝕜 :=
  (Submodule.quotEquivOfEq _ _ (jamesBidualLimit_ker_eq (𝕜 := 𝕜) p hp hpl).symm).trans
    ((jamesBidualLimitLinear (𝕜 := 𝕜) p hp).quotKerEquivOfSurjective
      (jamesBidualLimit_surjective p hp hpl))

include hp in
/-- Quasi-reflexivity of order one for the actual finite-path James norm. -/
theorem jamesSequence_quasiReflexive_orderOne (hpl : 1 < p.val.toReal) :
    IsQuasiReflexiveOfOrderOne 𝕜 (JamesSequenceSpace 𝕜 p) := by
  exact Module.rank_eq_one_iff_finrank_eq_one.mpr
    ((jamesResiduumScalarEquiv (𝕜 := 𝕜) p hp hpl).finrank_eq.trans (Module.finrank_self 𝕜))

end ThesisCommon
