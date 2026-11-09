import JFA.CZeroDiscreteProduct
import JFA.Definitions
import ThesisCommon.Analysis.FiniteCoefficientAbsorption
import Mathlib.Topology.Constructions.SumProd

/-! Identifications between the C₀ product models used in Lemma 4.6. -/

noncomputable section
open TopologicalSpace
open scoped ZeroAtInfty
namespace JFA

variable {𝕜 : Type*} [RCLike 𝕜]

def czeroHomeomorphIsometry {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]
    (e : K ≃ₜ L) : C₀(K, 𝕜) ≃ₗᵢ[𝕜] C₀(L, 𝕜) where
  toFun f := f.comp e.symm.toCocompactMap
  invFun f := f.comp e.toCocompactMap
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := by intro f; ext k; exact congrArg f (e.symm_apply_apply k)
  right_inv := by intro f; ext l; exact congrArg f (e.apply_symm_apply l)
  norm_map' := by
    intro f
    apply le_antisymm
    · exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
        fun l => f.toBCF.norm_coe_le_norm (e.symm l)
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
      intro k
      have h := (f.comp e.symm.toCocompactMap).toBCF.norm_coe_le_norm (e k)
      change ‖f (e.symm (e k))‖ ≤ _ at h
      rwa [e.symm_apply_apply] at h

def czeroCompactIsometry {M : Type*} [TopologicalSpace M] [CompactSpace M] :
    C₀(M, 𝕜) ≃ₗᵢ[𝕜] C(M, 𝕜) where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty.symm
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  norm_map' := by intros; rfl

def continuousMapValueEquiv {M E F : Type*} [TopologicalSpace M] [CompactSpace M]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) : C(M, E) ≃L[𝕜] C(M, F) :=
  ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.compLeftContinuous 𝕜 M e.toContinuousLinearMap)
    (ContinuousLinearMap.compLeftContinuous 𝕜 M e.symm.toContinuousLinearMap)
    (fun f => ContinuousMap.ext fun m => e.symm_apply_apply (f m))
    (fun f => ContinuousMap.ext fun m => e.apply_symm_apply (f m))

/-- The c₀-sum presentation of C₀(M × ℕ) for compact M. -/
def czeroCompactNatEquiv {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M] :
    C₀(M × ℕ, 𝕜) ≃L[𝕜] C₀(ℕ, C(M, 𝕜)) :=
  ((czeroHomeomorphIsometry (Homeomorph.prodComm M ℕ)).trans
    czeroDiscreteProductEquiv).toContinuousLinearEquiv.trans
      (ThesisCommon.cZeroMapEquiv (ι := ℕ) czeroCompactIsometry.toContinuousLinearEquiv)

/-- A nonempty finite compact factor gives scalar c₀. -/
def czeroFiniteCompactNatEquiv {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [Finite M] [Nonempty M] : C₀(M × ℕ, 𝕜) ≃L[𝕜] cZero 𝕜 := by
  letI : DiscreteTopology M := Finite.instDiscreteTopology
  letI := Fintype.ofFinite M
  let e : C(M, 𝕜) ≃L[𝕜] (M → 𝕜) :=
    (czeroCompactIsometry (𝕜 := 𝕜) (M := M)).symm.toContinuousLinearEquiv.trans
      ((ThesisCommon.finiteFunctionCZeroIsometry (𝕜 := 𝕜) (X := 𝕜) M).symm.toContinuousLinearEquiv)
  letI : FiniteDimensional 𝕜 C(M, 𝕜) :=
    FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.injective
  letI : Nontrivial C(M, 𝕜) := e.symm.injective.nontrivial
  exact czeroCompactNatEquiv.trans (ThesisCommon.cZeroFiniteCoefficientEquiv (Γ := ℕ))

end JFA
