import Posets.FunctionalFamilySupport
import Posets.MrowkaLimits

/-! The reduced matrix agrees with the operator on all but countably many
family indicators. The residual coordinate functional kills isolated vectors. -/

noncomputable section
open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 ℬ : Set (Set ℕ)}

def naturalRestriction (𝒜 : Set (Set ℕ)) : Space 𝕜 𝒜 →L[𝕜] (ℕ →ᵇ 𝕜) :=
  ({ toFun f := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        (fun n => f (Sum.inl n)) ‖f‖ (fun n => f.toBCF.norm_coe_le_norm _)
     map_add' f g := by ext n; rfl
     map_smul' c f := by ext n; rfl } : Space 𝕜 𝒜 →ₗ[𝕜] (ℕ →ᵇ 𝕜)).mkContinuous 1
    (fun f => by
      simpa only [one_mul] using (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
        (fun n => f.toBCF.norm_coe_le_norm (Sum.inl n)))

@[simp] theorem naturalRestriction_apply (f : Space 𝕜 𝒜) (n : ℕ) :
    naturalRestriction 𝒜 f n = f (Sum.inl n) := rfl

def residualCoordinate (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (k : ℕ) :
    Space 𝕜 𝒜 →L[𝕜] 𝕜 :=
  (JLMS.evaluation (K := Mrowka ℬ) (Sum.inl k)).comp T -
    (BoundedContinuousFunction.evalCLM 𝕜 k).comp
      ((matrixOperator (reducedMatrix 𝕜 T)
        ⟨reducedMatrix_row_summable T, ‖T‖, reducedMatrix_row_bound T⟩).comp (naturalRestriction 𝒜))

theorem residualCoordinate_apply (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (k : ℕ) (f : Space 𝕜 𝒜) :
    residualCoordinate T k f = T f (Sum.inl k) -
      matrixAction 𝕜 (reducedMatrix 𝕜 T) (fun n => f (Sum.inl n)) k := rfl

theorem residualCoordinate_isolated (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (k n : ℕ) :
    residualCoordinate T k (isolatedVector 𝕜 𝒜 n) = 0 := by
  rw [residualCoordinate_apply]
  unfold matrixAction
  rw [tsum_eq_single n (fun m hm => by simp [isolatedVector_natural, hm])]
  simp [isolatedVector_natural, reducedMatrix]

def operatorExceptionalFamily (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) : Set 𝒜 :=
  ⋃ k : ℕ, {A : 𝒜 | residualCoordinate T k (familyVector 𝕜 𝒜 h𝒜 A) ≠ 0}

theorem operatorExceptionalFamily_countable (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) : (operatorExceptionalFamily h𝒜 T).Countable :=
  Set.countable_iUnion (fun k => functional_family_support_countable h𝒜
    (residualCoordinate T k) (residualCoordinate_isolated T k))

theorem operator_family_matrix (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (A : 𝒜)
    (hA : A ∉ operatorExceptionalFamily h𝒜 T) (k : ℕ) :
    T (familyVector 𝕜 𝒜 h𝒜 A) (Sum.inl k) =
      matrixAction 𝕜 (reducedMatrix 𝕜 T) (indicator 𝕜 A.val) k := by
  have hz : residualCoordinate T k (familyVector 𝕜 𝒜 h𝒜 A) = 0 := by
    by_contra hn
    exact hA (Set.mem_iUnion.mpr ⟨k, hn⟩)
  rw [residualCoordinate_apply] at hz
  simpa only [familyVector_natural] using sub_eq_zero.mp hz

theorem operator_family_matrix_tendsto (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (A : 𝒜)
    (hA : A ∉ operatorExceptionalFamily h𝒜 T) (B : ℬ) :
    Tendsto (matrixAction 𝕜 (reducedMatrix 𝕜 T) (indicator 𝕜 A.val)) (Along B.val)
      (𝓝 (T (familyVector 𝕜 𝒜 h𝒜 A) (Sum.inr B))) := by
  have h := (T (familyVector 𝕜 𝒜 h𝒜 A)).continuous.continuousAt.tendsto.comp
    (family_tendsto_along ℬ B)
  change Tendsto (fun k => T (familyVector 𝕜 𝒜 h𝒜 A) (Sum.inl k)) (Along B.val)
    (𝓝 (T (familyVector 𝕜 𝒜 h𝒜 A) (Sum.inr B))) at h
  simpa only [operator_family_matrix h𝒜 T A hA] using h

end Posets
