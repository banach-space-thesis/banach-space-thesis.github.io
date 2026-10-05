import JLMS.MatrixAutomaticContinuity
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# Section 9: automatic continuity for operators on finite powers

Each operator on a finite power is the finite sum of its matrix corners.
Diagonal corners are algebra homomorphisms; each off-diagonal corner is a
diagonal corner times a fixed matrix unit. This is the paper's matrix argument
applied directly to bounded operators on the product Banach space.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

def operatorFiniteCorner (i j : ι) (T : E →L[𝕜] E) :
    (ι → E) →L[𝕜] (ι → E) :=
  (ContinuousLinearMap.single 𝕜 (fun _ : ι => E) i).comp
    (T.comp (ContinuousLinearMap.proj j))

@[simp] theorem operatorFiniteCorner_apply (i j : ι) (T : E →L[𝕜] E) (x : ι → E) :
    operatorFiniteCorner i j T x = Pi.single i (T (x j)) := rfl

def operatorFiniteDiagonal (i : ι) : (E →L[𝕜] E) →ₙₐ[𝕜] ((ι → E) →L[𝕜] (ι → E)) where
  toFun := operatorFiniteCorner i i
  map_zero' := by ext x k; simp [Pi.single]
  map_add' S T := by
    ext x k
    by_cases h : k = i
    · subst k; simp
    · simp [Pi.single, Function.update_of_ne h]
  map_smul' c T := by
    ext x k
    by_cases h : k = i
    · subst k; simp
    · simp [Pi.single, Function.update_of_ne h]
  map_mul' S T := by ext x k; simp [ContinuousLinearMap.mul_apply]

theorem operatorFiniteCorner_eq_diagonal_mul (i j : ι) (T : E →L[𝕜] E) :
    operatorFiniteCorner i j T =
      (operatorFiniteDiagonal (𝕜 := 𝕜) (E := E) i) T * operatorFiniteCorner i j (ContinuousLinearMap.id 𝕜 E) := by
  ext x k
  simp [operatorFiniteDiagonal, ContinuousLinearMap.mul_apply]

theorem operator_eq_sum_finiteCorners (T : (ι → E) →L[𝕜] (ι → E)) :
    T = ∑ i, ∑ j, operatorFiniteCorner i j
      ((ContinuousLinearMap.proj i).comp
        (T.comp (ContinuousLinearMap.single 𝕜 (fun _ : ι => E) j))) := by
  have hid : (∑ i : ι, operatorFiniteCorner i i (ContinuousLinearMap.id 𝕜 E)) =
      ContinuousLinearMap.id 𝕜 (ι → E) := by
    ext x k
    simp [ContinuousLinearMap.sum_apply, Pi.single_apply]
  calc
    T = (∑ i : ι, operatorFiniteCorner i i (ContinuousLinearMap.id 𝕜 E)) * T *
        (∑ j : ι, operatorFiniteCorner j j (ContinuousLinearMap.id 𝕜 E)) := by
      rw [hid]
      ext x k; rfl
    _ = ∑ i, ∑ j, operatorFiniteCorner i i (ContinuousLinearMap.id 𝕜 E) * T *
        operatorFiniteCorner j j (ContinuousLinearMap.id 𝕜 E) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ext x k
      simp [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]

theorem continuous_operator_hom_of_finitePower
    (hE : ∀ ψ : (E →L[𝕜] E) →ₙₐ[𝕜] A, Continuous ψ)
    (φ : ((ι → E) →L[𝕜] (ι → E)) →ₙₐ[𝕜] A) : Continuous φ := by
  have hcorner (i j : ι) : Continuous (fun T : E →L[𝕜] E => φ (operatorFiniteCorner i j T)) := by
    have h := hE (φ.comp (operatorFiniteDiagonal i))
    have heq (T : E →L[𝕜] E) : φ (operatorFiniteCorner i j T) =
        φ.comp (operatorFiniteDiagonal i) T * φ (operatorFiniteCorner i j (ContinuousLinearMap.id 𝕜 E)) := by
      rw [operatorFiniteCorner_eq_diagonal_mul, map_mul]; rfl
    convert h.mul (continuous_const (y := φ (operatorFiniteCorner i j (ContinuousLinearMap.id 𝕜 E)))) using 1
    funext T; exact heq T
  have hsum : Continuous (fun T : (ι → E) →L[𝕜] (ι → E) => ∑ i, ∑ j,
      φ (operatorFiniteCorner i j ((ContinuousLinearMap.proj i).comp
        (T.comp (ContinuousLinearMap.single 𝕜 (fun _ : ι => E) j))))) := by
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro j hj
    apply (hcorner i j).comp
    exact ((continuous_id (X := (ι → E) →L[𝕜] (ι → E))).clm_comp_const
      (ContinuousLinearMap.single 𝕜 (fun _ : ι => E) j)).const_clm_comp
        (ContinuousLinearMap.proj i : (ι → E) →L[𝕜] E)
  convert hsum using 1
  funext T
  conv_lhs => rw [operator_eq_sum_finiteCorners T]
  simp only [map_sum]

end JLMS
