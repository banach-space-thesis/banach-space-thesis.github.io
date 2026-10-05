import Posets.OrdinalBandCompressionEstimates
import Posets.WolfeOperatorRows
import Mathlib.Topology.Sets.Compacts

/-! Atomic mass controls the actual operator norm on the entire subspace
of continuous functions supported in a prescribed set. -/
noncomputable section
namespace Posets
open Set Topology TopologicalSpace
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def cZeroSupportedOn (U : Set K) : Submodule 𝕜 (JLMS.CZero 𝕜 K) where
  carrier := {f | ∀ x, x ∉ U → f x = 0}
  zero_mem' := by intro x hx; rfl
  add_mem' := by
    intro f g hf hg x hx
    change f x + g x = 0
    rw [hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro a f hf x hx
    change a • f x = 0
    rw [hf x hx, smul_zero]

theorem cZeroSupportedOn_support {U : Set K} (f : cZeroSupportedOn (𝕜 := 𝕜) U) :
    Function.support f.val ⊆ U := by
  intro x hx
  by_contra hn
  exact hx (f.property x hn)

theorem cZeroSupportedOn_isClosed (U : Set K) :
    IsClosed (cZeroSupportedOn (𝕜 := 𝕜) U : Set (JLMS.CZero 𝕜 K)) := by
  have heq : (cZeroSupportedOn (𝕜 := 𝕜) U : Set (JLMS.CZero 𝕜 K)) =
      ⋂ x, ⋂ (_ : x ∉ U), {f | (JLMS.evaluation x) f = (0 : 𝕜)} := by
    ext f
    change (∀ x, x ∉ U → f x = 0) ↔ _
    simp only [Set.mem_setOf_eq, Set.mem_iInter, JLMS.evaluation_apply]
  rw [heq]
  exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
    isClosed_eq (JLMS.evaluation x).continuous continuous_const))

def cZeroSupportedRead (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (C : Compacts K) (U : Set K) : cZeroSupportedOn (𝕜 := 𝕜) U →L[𝕜] C(C, 𝕜) :=
  (ordinalBandRead (𝕜 := 𝕜) ⟨Subtype.val, continuous_subtype_val⟩).comp
    (T.comp (cZeroSupportedOn (𝕜 := 𝕜) U).subtypeL)

@[simp] theorem cZeroSupportedRead_apply
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (C : Compacts K) (U : Set K)
    (f : cZeroSupportedOn (𝕜 := 𝕜) U) (x : C) :
    cZeroSupportedRead T C U f x = T f.val x.val := rfl

theorem cZero_operator_apply_le_of_supported_mass (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) {U : Set K}
    (g : JLMS.CZero 𝕜 K) (hg : Function.support g ⊆ U) (x : K)
    {ε : ℝ} (hm : wolfeMass M (wolfeOperatorRow T x) U ≤ ε) :
    ‖T g x‖ ≤ ε * ‖g‖ := by
  let φ : JLMS.CZero 𝕜 K →L[𝕜] 𝕜 := (JLMS.evaluation x).comp T
  change ‖φ g‖ ≤ ε * ‖g‖
  rw [← ordinalBand_atomic_apply_of_support M φ g hg]
  exact ((JLMS.atomicRestriction M U φ).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right hm (norm_nonneg g))

theorem norm_cZeroSupportedRead_le_of_mass (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (C : Compacts K) (U : Set K)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hm : ∀ x : C, wolfeMass M (wolfeOperatorRow T x.val) U ≤ ε) :
    ‖cZeroSupportedRead T C U‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hε (norm_nonneg f))).mpr
  intro x
  exact cZero_operator_apply_le_of_supported_mass M T f.val
    (cZeroSupportedOn_support f) x.val (hm x)

end Posets
