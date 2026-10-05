import JLMS.AtomicSynthesis
import JLMS.RealAtomicRepresentation
import JLMS.CZeroScalarParts

/-!
# Rudin's theorem for scattered locally compact Hausdorff spaces

Positive decomposition and Riesz representation give the real existence
proof. Scalar real/imaginary decomposition gives existence over either
scalar field. Isometric atomic synthesis then gives the full linear isometric
equivalence, with the required agreement on point evaluations.
-/

noncomputable section

attribute [local instance] Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]

local instance rudinDualGroup : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance rudinDualSpace : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

/-- Embedding real ℓ¹ coefficients into the chosen scalar field. -/
def ofRealEllOne (a : ellOneOn ℝ K) : ellOneOn 𝕜 K :=
  ⟨fun x => (a x : 𝕜), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, RCLike.norm_ofReal,
      ← Real.norm_eq_abs] using ellOneOn_summable_norm a⟩

omit [TopologicalSpace K] in
@[simp] theorem ofRealEllOne_apply (a : ellOneOn ℝ K) (x : K) :
    ofRealEllOne (𝕜 := 𝕜) a x = (a x : 𝕜) := rfl

theorem atomicFunctional_ofReal (a : ellOneOn ℝ K) (f : CZero ℝ K) :
    atomicFunctional (ofRealEllOne (𝕜 := 𝕜) a) (ofRealCZero f) =
      (atomicFunctional a f : 𝕜) := by
  change (∑' x : K, (a x : 𝕜) * (f x : 𝕜)) = ((∑' x : K, a x * f x : ℝ) : 𝕜)
  simp_rw [← RCLike.ofReal_mul]
  exact ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).map_tsum (summable_atomic_values a f)).symm

variable [LocallyCompactSpace K] [T2Space K]

/-- Atomic synthesis represents every bounded functional, over ℝ or ℂ.
The measurable structure is chosen internally; it is not a new hypothesis. -/
theorem atomicSynthesis_surjective (hK : IsScattered K) :
    Function.Surjective (atomicSynthesis (𝕜 := 𝕜) (K := K)) := by
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  intro φ
  let P : CZero ℝ K →L[ℝ] ℝ := RCLike.reCLM.comp
    ((φ.restrictScalars ℝ).comp (ofRealCZeroCLM (𝕜 := 𝕜) (K := K)))
  let Q : CZero ℝ K →L[ℝ] ℝ := RCLike.imCLM.comp
    ((φ.restrictScalars ℝ).comp (ofRealCZeroCLM (𝕜 := 𝕜) (K := K)))
  obtain ⟨a, ha⟩ := exists_real_atomic_representation hK P
  obtain ⟨b, hb⟩ := exists_real_atomic_representation hK Q
  let c := ofRealEllOne (𝕜 := 𝕜) a + (RCLike.I : 𝕜) • ofRealEllOne (𝕜 := 𝕜) b
  have hreal (f : CZero ℝ K) : φ (ofRealCZero f) = atomicFunctional c (ofRealCZero f) := by
    have hr : RCLike.re (φ (ofRealCZero f)) = atomicFunctional a f := ha f
    have hi : RCLike.im (φ (ofRealCZero f)) = atomicFunctional b f := hb f
    have hc : atomicFunctional c = atomicFunctional (ofRealEllOne (𝕜 := 𝕜) a) +
        (RCLike.I : 𝕜) • atomicFunctional (ofRealEllOne (𝕜 := 𝕜) b) := by
      change atomicSynthesis (𝕜 := 𝕜) (K := K)
        (ofRealEllOne a + (RCLike.I : 𝕜) • ofRealEllOne b) = _
      rw [map_add, map_smul]
      rfl
    rw [hc]
    change φ (ofRealCZero f) =
      atomicFunctional (ofRealEllOne a) (ofRealCZero f) +
        RCLike.I * atomicFunctional (ofRealEllOne b) (ofRealCZero f)
    rw [atomicFunctional_ofReal, atomicFunctional_ofReal, ← hr, ← hi, mul_comm]
    exact (RCLike.re_add_im _).symm
  refine ⟨c, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  have hd := real_imaginary_decomposition f
  change atomicFunctional c f = φ f
  calc
    atomicFunctional c f = atomicFunctional c
        (ofRealCZero (realPartCZero f) + (RCLike.I : 𝕜) • ofRealCZero (imaginaryPartCZero f)) :=
      congrArg (atomicFunctional c) hd.symm
    _ = φ (ofRealCZero (realPartCZero f) + (RCLike.I : 𝕜) • ofRealCZero (imaginaryPartCZero f)) := by
      simp only [map_add, map_smul, ← hreal]
    _ = φ f := congrArg φ hd

/-- The full Rudin representation, including the point-mass identification
needed for supports and atomic restrictions in Sections 4–7. -/
theorem exists_atomicDualModel (hK : IsScattered K) : Nonempty (AtomicDualModel 𝕜 K) := by
  let S : ellOneOn 𝕜 K →ₗᵢ[𝕜] (CZero 𝕜 K →L[𝕜] 𝕜) :=
    { (atomicSynthesis (𝕜 := 𝕜) (K := K)).toLinearMap with
      norm_map' := norm_atomicFunctional hK }
  let e := LinearIsometryEquiv.ofSurjective S (atomicSynthesis_surjective (𝕜 := 𝕜) hK)
  refine ⟨⟨e.symm, ?_⟩⟩
  intro x
  change atomicFunctional (lp.single 1 x (1 : 𝕜)) = evaluation x
  simp

/-- Discharge the representation input previously isolated by the project. -/
theorem rudinRepresentation : RudinRepresentation 𝕜 K := exists_atomicDualModel

end JLMS
