import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Module.StrongTopology

/-! Concrete change of an isometrically isomorphic scalar field on
continuous functions, their duals, measure Lp spaces, and lp families.
Every equivalence acts pointwise or by conjugation, preserving the actual
norms. These semilinear maps compose to linear maps over the original field. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv
variable {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
variable (e : 𝕜 ≃+* 𝕜') [RingHomIsometric (RingHomClass.toRingHom e)] [RingHomIsometric (RingHomClass.toRingHom e.symm)]

local instance : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
  simpa only [RingEquiv.symm_symm] using (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))

omit [RingHomIsometric (RingHomClass.toRingHom e.symm)] in
theorem scalarRingEquiv_norm (x : 𝕜) : ‖e x‖ = ‖x‖ :=
  RingHomIsometric.norm_map (σ := (RingHomClass.toRingHom e))

def scalarRingIsometryEquiv : 𝕜 ≃ₛₗᵢ[(RingHomClass.toRingHom e)] 𝕜' where
  toEquiv := e.toEquiv
  map_add' := e.map_add
  map_smul' := e.map_mul
  norm_map' := scalarRingEquiv_norm e

def continuousMapScalarIsometryEquiv (K : Type*) [TopologicalSpace K] [CompactSpace K] :
    C(K, 𝕜) ≃ₛₗᵢ[(RingHomClass.toRingHom e)] C(K, 𝕜') where
  toFun f := ⟨fun x => e (f x), (scalarRingIsometryEquiv e).continuous.comp f.continuous⟩
  invFun f := ⟨fun x => e.symm (f x), (scalarRingIsometryEquiv e.symm).continuous.comp f.continuous⟩
  left_inv f := by ext x; exact e.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.apply_symm_apply (f x)
  map_add' f g := by ext x; exact e.map_add (f x) (g x)
  map_smul' c f := by ext x; exact e.map_mul c (f x)
  norm_map' f := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      exact (scalarRingEquiv_norm e (f x)).le.trans (f.norm_coe_le_norm x)
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      rw [← scalarRingEquiv_norm e (f x)]
      exact ContinuousMap.norm_coe_le_norm
        ⟨fun x => e (f x), (scalarRingIsometryEquiv e).continuous.comp f.continuous⟩ x

def continuousMapDualScalarEquiv (K : Type*) [TopologicalSpace K] [CompactSpace K] :
    (C(K, 𝕜) →L[𝕜] 𝕜) ≃SL[(RingHomClass.toRingHom e)] (C(K, 𝕜') →L[𝕜'] 𝕜') :=
  (continuousMapScalarIsometryEquiv e K).toContinuousLinearEquiv.arrowCongrSL
    (scalarRingIsometryEquiv e).toContinuousLinearEquiv

theorem continuousMapDualScalarEquiv_norm (K : Type*) [TopologicalSpace K] [CompactSpace K]
    (φ : C(K, 𝕜) →L[𝕜] 𝕜) : ‖continuousMapDualScalarEquiv e K φ‖ = ‖φ‖ := by
  let F := continuousMapScalarIsometryEquiv e K
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
    intro f
    change ‖e (φ (F.symm f))‖ ≤ _
    rw [scalarRingEquiv_norm]
    exact (φ.le_opNorm _).trans_eq (by rw [F.symm.norm_map])
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have h := (continuousMapDualScalarEquiv e K φ).le_opNorm (F f)
    change ‖e (φ (F.symm (F f)))‖ ≤ _ at h
    simpa only [F.symm_apply_apply, scalarRingEquiv_norm, F.norm_map] using h

def continuousMapDualScalarIsometryEquiv (K : Type*) [TopologicalSpace K] [CompactSpace K] :
    (C(K, 𝕜) →L[𝕜] 𝕜) ≃ₛₗᵢ[(RingHomClass.toRingHom e)] (C(K, 𝕜') →L[𝕜'] 𝕜') where
  toLinearEquiv := (continuousMapDualScalarEquiv e K).toLinearEquiv
  norm_map' := continuousMapDualScalarEquiv_norm e K

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

def measureLpScalarMap : Lp 𝕜 p μ →SL[(RingHomClass.toRingHom e)] Lp 𝕜' p μ :=
  (scalarRingIsometryEquiv e).toContinuousLinearEquiv.toContinuousLinearMap.compLpL p μ

omit [RingHomIsometric (RingHomClass.toRingHom e.symm)] in
theorem measureLpScalarMap_coe (f : Lp 𝕜 p μ) :
    measureLpScalarMap e μ p f =ᵐ[μ] fun x => e (f x) :=
  ContinuousLinearMap.coeFn_compLpL _ f

theorem measureLpScalarMap_inverse (f : Lp 𝕜 p μ) :
    measureLpScalarMap e.symm μ p (measureLpScalarMap e μ p f) = f := by
  apply Lp.ext
  filter_upwards [measureLpScalarMap_coe e.symm μ p (measureLpScalarMap e μ p f),
    measureLpScalarMap_coe e μ p f] with x hx hy
  rw [hx, hy, e.symm_apply_apply]

omit [RingHomIsometric (RingHomClass.toRingHom e.symm)] in
theorem measureLpScalarMap_norm (f : Lp 𝕜 p μ) :
    ‖measureLpScalarMap e μ p f‖ = ‖f‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [measureLpScalarMap_coe e μ p f] with x hx
    rw [hx, scalarRingEquiv_norm]
  · filter_upwards [measureLpScalarMap_coe e μ p f] with x hx
    rw [hx, scalarRingEquiv_norm]

def measureLpScalarIsometryEquiv : Lp 𝕜 p μ ≃ₛₗᵢ[(RingHomClass.toRingHom e)] Lp 𝕜' p μ where
  toFun := measureLpScalarMap e μ p
  invFun := measureLpScalarMap e.symm μ p
  left_inv := measureLpScalarMap_inverse e μ p
  right_inv := measureLpScalarMap_inverse e.symm μ p
  map_add' := map_add (measureLpScalarMap e μ p)
  map_smul' := map_smulₛₗ (measureLpScalarMap e μ p)
  norm_map' := measureLpScalarMap_norm e μ p

section Family
variable {ι : Type*} {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜' (F i)]

def lpFamilySemilinearValue (hp : 0 < p.toReal) (a : ∀ i, E i ≃ₛₗᵢ[(RingHomClass.toRingHom e)] F i)
    (x : lp E p) : lp F p :=
  ⟨fun i => a i (x i), (memℓp_gen_iff hp).mpr (by
    simpa only [LinearIsometryEquiv.norm_map] using (lp.memℓp x).summable hp)⟩

def lpFamilySemilinearIsometryEquiv (hp : 0 < p.toReal)
    (a : ∀ i, E i ≃ₛₗᵢ[(RingHomClass.toRingHom e)] F i) : lp E p ≃ₛₗᵢ[(RingHomClass.toRingHom e)] lp F p where
  toFun := lpFamilySemilinearValue e p hp a
  invFun := lpFamilySemilinearValue e.symm p hp (fun i => (a i).symm)
  left_inv x := by apply lp.ext; funext i; exact (a i).symm_apply_apply (x i)
  right_inv x := by apply lp.ext; funext i; exact (a i).apply_symm_apply (x i)
  map_add' x y := by apply lp.ext; funext i; exact map_add (a i) (x i) (y i)
  map_smul' c x := by apply lp.ext; funext i; exact map_smulₛₗ (a i) c (x i)
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    apply tsum_congr
    intro i
    change ‖a i (x i)‖ ^ p.toReal = ‖x i‖ ^ p.toReal
    rw [LinearIsometryEquiv.norm_map]
end Family

end ThesisCommon

