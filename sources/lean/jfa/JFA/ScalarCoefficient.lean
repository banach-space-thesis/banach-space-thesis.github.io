import JFA.SeparableIdeal
import Mathlib.Analysis.Normed.Ring.Units

/-! The scalar quotient map for a nonseparable Banach space with few operators.
Its existence, linearity, multiplicativity, and contractive bound are proved;
none of them is an extra hypothesis supplied to the tensor decomposition. -/

noncomputable section
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem one_le_norm_id_sub_separable [CompleteSpace X] (hX : ¬ SeparableSpace X)
    (S : X →L[𝕜] X) (hS : HasSeparableRange 𝕜 X X S) :
    1 ≤ ‖ContinuousLinearMap.id 𝕜 X - S‖ := by
  by_contra h
  have hsmall : ‖1 - S‖ < 1 := lt_of_not_ge h
  have hunit : IsUnit S := by
    have hu := (Units.oneSub (1 - S) hsmall).isUnit
    simpa only [Units.val_oneSub, sub_sub_cancel] using hu
  obtain ⟨u, hu⟩ := hunit
  have hsep := hS.comp_left (↑u⁻¹ : X →L[𝕜] X)
  have heq : (↑u⁻¹ : X →L[𝕜] X).comp S = ContinuousLinearMap.id 𝕜 X := by
    change (↑u⁻¹ : X →L[𝕜] X) * S = 1
    rw [← hu]
    exact u.inv_val
  rw [heq] at hsep
  have hz := (scalar_id_separable_iff hX (1 : 𝕜)).mp (by simpa using hsep)
  exact one_ne_zero hz

theorem scalar_norm_le [CompleteSpace X] (hX : ¬ SeparableSpace X)
    {T S : X →L[𝕜] X} {a : 𝕜} (hS : HasSeparableRange 𝕜 X X S)
    (hT : T = a • ContinuousLinearMap.id 𝕜 X + S) : ‖a‖ ≤ ‖T‖ := by
  by_cases ha : a = 0
  · simp [ha]
  have heq : ContinuousLinearMap.id 𝕜 X - (-a⁻¹ • S) = a⁻¹ • T := by
    rw [hT, smul_add, smul_smul]
    simp [ha, sub_eq_add_neg]
  have h := one_le_norm_id_sub_separable hX (-a⁻¹ • S) (hS.smul _)
  rw [heq, norm_smul, norm_inv, ← div_eq_inv_mul] at h
  simpa using (le_div_iff₀ (norm_pos_iff.mpr ha)).mp h

def scalarCoefficient (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : X →L[𝕜] X) : 𝕜 :=
  (Classical.choose (fewOperators_unique_decomposition hX hfew T).exists).1

def scalarRemainder (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : X →L[𝕜] X) : X →L[𝕜] X :=
  (Classical.choose (fewOperators_unique_decomposition hX hfew T).exists).2

theorem scalarRemainder_separable (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : X →L[𝕜] X) : HasSeparableRange 𝕜 X X (scalarRemainder hX hfew T) :=
  (Classical.choose_spec (fewOperators_unique_decomposition hX hfew T).exists).1

theorem scalar_decomposition (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : X →L[𝕜] X) : T = scalarCoefficient hX hfew T • ContinuousLinearMap.id 𝕜 X +
      scalarRemainder hX hfew T :=
  (Classical.choose_spec (fewOperators_unique_decomposition hX hfew T).exists).2

theorem scalarCoefficient_eq (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    {T S : X →L[𝕜] X} {a : 𝕜} (hS : HasSeparableRange 𝕜 X X S)
    (hT : T = a • ContinuousLinearMap.id 𝕜 X + S) : scalarCoefficient hX hfew T = a :=
  scalar_decomposition_unique hX (scalarRemainder_separable hX hfew T) hS
    (scalar_decomposition hX hfew T) hT

theorem scalarCoefficient_add (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (S T : X →L[𝕜] X) : scalarCoefficient hX hfew (S + T) =
      scalarCoefficient hX hfew S + scalarCoefficient hX hfew T := by
  apply scalarCoefficient_eq hX hfew
    ((scalarRemainder_separable hX hfew S).add (scalarRemainder_separable hX hfew T))
  calc
    S + T = (scalarCoefficient hX hfew S • ContinuousLinearMap.id 𝕜 X +
        scalarRemainder hX hfew S) +
        (scalarCoefficient hX hfew T • ContinuousLinearMap.id 𝕜 X +
        scalarRemainder hX hfew T) :=
      congrArg₂ (· + ·) (scalar_decomposition hX hfew S) (scalar_decomposition hX hfew T)
    _ = _ := by rw [add_smul]; abel

theorem scalarCoefficient_smul (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (a : 𝕜) (T : X →L[𝕜] X) : scalarCoefficient hX hfew (a • T) =
      a * scalarCoefficient hX hfew T := by
  apply scalarCoefficient_eq hX hfew ((scalarRemainder_separable hX hfew T).smul a)
  calc
    a • T = a • (scalarCoefficient hX hfew T • ContinuousLinearMap.id 𝕜 X +
        scalarRemainder hX hfew T) := congrArg (a • ·) (scalar_decomposition hX hfew T)
    _ = _ := by rw [smul_add, smul_smul]

theorem scalarCoefficient_norm_le [CompleteSpace X] (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (T : X →L[𝕜] X) : ‖scalarCoefficient hX hfew T‖ ≤ ‖T‖ :=
  scalar_norm_le hX (scalarRemainder_separable hX hfew T) (scalar_decomposition hX hfew T)

def scalarCoefficientL [CompleteSpace X] (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X) :
    (X →L[𝕜] X) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous {
    toFun := scalarCoefficient hX hfew
    map_add' := scalarCoefficient_add hX hfew
    map_smul' := fun a T => by
      simpa [smul_eq_mul] using scalarCoefficient_smul hX hfew a T }
    1 (fun T => by simpa using scalarCoefficient_norm_le hX hfew T)

@[simp] theorem scalarCoefficient_id (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) :
    scalarCoefficient hX hfew (ContinuousLinearMap.id 𝕜 X) = 1 := by
  apply scalarCoefficient_eq hX hfew (hasSeparableRange_zero (𝕜 := 𝕜) (E := X) (F := X))
  simp

theorem scalarCoefficient_comp (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) (T U : X →L[𝕜] X) :
    scalarCoefficient hX hfew (T.comp U) =
      scalarCoefficient hX hfew T * scalarCoefficient hX hfew U := by
  apply scalarCoefficient_eq hX hfew
    (((scalarRemainder_separable hX hfew T).smul (scalarCoefficient hX hfew U)).add
      ((scalarRemainder_separable hX hfew U).comp_left T))
  calc
    T.comp U = T.comp (scalarCoefficient hX hfew U • ContinuousLinearMap.id 𝕜 X +
        scalarRemainder hX hfew U) := congrArg T.comp (scalar_decomposition hX hfew U)
    _ = scalarCoefficient hX hfew U • T + T.comp (scalarRemainder hX hfew U) := by
      simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul,
        ContinuousLinearMap.comp_id]
    _ = scalarCoefficient hX hfew U •
        (scalarCoefficient hX hfew T • ContinuousLinearMap.id 𝕜 X +
        scalarRemainder hX hfew T) + T.comp (scalarRemainder hX hfew U) :=
      congrArg (fun V => scalarCoefficient hX hfew U • V +
        T.comp (scalarRemainder hX hfew U)) (scalar_decomposition hX hfew T)
    _ = _ := by rw [smul_add, smul_smul, mul_comm]; exact add_assoc _ _ _

theorem scalarCoefficient_eq_zero_iff (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) (T : X →L[𝕜] X) :
    scalarCoefficient hX hfew T = 0 ↔ HasSeparableRange 𝕜 X X T := by
  constructor
  · intro h
    have hT : T = scalarRemainder hX hfew T := by
      simpa only [h, zero_smul, zero_add] using scalar_decomposition hX hfew T
    exact hT ▸ scalarRemainder_separable hX hfew T
  · intro hT
    apply scalarCoefficient_eq hX hfew hT
    simp

end JFA
