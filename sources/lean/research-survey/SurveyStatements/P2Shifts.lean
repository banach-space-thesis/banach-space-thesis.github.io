import SurveyStatements.P2Calkin
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The concrete prefix and removal operators from the second proof. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P2
universe u
variable (Γ : Type u)

instance wordTopology : TopologicalSpace (List Γ) := ⊥
instance wordDiscreteTopology : DiscreteTopology (List Γ) := ⟨rfl⟩

/-- The source's space `c₀(Γ^{<ω})`, with its genuine supremum norm. -/
abbrev WordC0 := ZeroAtInftyContinuousMap (List Γ) ℂ

variable {Γ}

local instance : DecidableEq Γ := Classical.decEq Γ

/-- A coordinate unit vector in the source's word space. -/
def wordUnit (w : List Γ) : WordC0 Γ where
  toFun v := if v = w then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply (tendsto_const_nhds :
      Tendsto (fun _ : List Γ => (0 : ℂ)) (cocompact (List Γ)) (𝓝 0)).congr'
    filter_upwards [(Set.finite_singleton w).isCompact.compl_mem_cocompact] with v hv
    have h : v ≠ w := hv
    simp [h]

@[simp] theorem wordUnit_apply (w v : List Γ) :
    wordUnit w v = if v = w then 1 else 0 := rfl

@[simp] theorem norm_wordUnit (w : List Γ) : ‖wordUnit w‖ = 1 := by
  apply le_antisymm
  · change ‖(wordUnit w).toBCF‖ ≤ 1
    apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro v
    change ‖wordUnit w v‖ ≤ 1
    by_cases h : v = w <;> simp [h]
  · have h := (wordUnit w).toBCF.norm_coe_le_norm w
    change ‖wordUnit w w‖ ≤ ‖wordUnit w‖ at h
    simpa [wordUnit] using h

/-- Insert a zero coordinate off the cylinder beginning with `a`. -/
def prefixC0 (a : Γ) (f : WordC0 Γ) : WordC0 Γ where
  toFun w := match w with
    | [] => 0
    | b :: v => if b = a then f v else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    classical
    apply tendsto_def.mpr
    intro U hU
    have hf : ∀ᶠ w in cofinite, f w ∈ U := by
      simpa only [← cocompact_eq_cofinite (List Γ)] using (zero_at_infty f).eventually hU
    have hK : {w : List Γ | f w ∉ U}.Finite := eventually_cofinite.mp hf
    rw [cocompact_eq_cofinite]
    filter_upwards [(hK.image (List.cons a)).compl_mem_cofinite] with w hw
    have hzero : (0 : ℂ) ∈ U := mem_of_mem_nhds hU
    cases w with
    | nil => exact hzero
    | cons b v =>
      change (if b = a then f v else 0) ∈ U
      by_cases hb : b = a
      · subst b
        simp only [if_pos rfl]
        by_contra hv
        exact hw ⟨v, hv, rfl⟩
      · simpa only [if_neg hb] using hzero

/-- Read the coordinates in the cylinder beginning with `a`. -/
def removalC0 (a : Γ) (f : WordC0 Γ) : WordC0 Γ where
  toFun w := f (a :: w)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply (zero_at_infty f).comp
    rw [cocompact_eq_cofinite]
    exact (List.cons_injective (a := a)).tendsto_cofinite

@[simp] theorem prefixC0_nil (a : Γ) (f : WordC0 Γ) : prefixC0 a f [] = 0 := rfl

@[simp] theorem prefixC0_cons (a b : Γ) (f : WordC0 Γ) (w : List Γ) :
    prefixC0 a f (b :: w) = if b = a then f w else 0 := rfl

@[simp] theorem removalC0_apply (a : Γ) (f : WordC0 Γ) (w : List Γ) :
    removalC0 a f w = f (a :: w) := rfl

theorem norm_prefixC0_le (a : Γ) (f : WordC0 Γ) : ‖prefixC0 a f‖ ≤ ‖f‖ := by
  change ‖(prefixC0 a f).toBCF‖ ≤ ‖f‖
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro w
  change ‖prefixC0 a f w‖ ≤ ‖f‖
  cases w with
  | nil => simp
  | cons b v =>
    by_cases h : b = a
    · simpa [h] using f.toBCF.norm_coe_le_norm v
    · simp [h]

theorem norm_removalC0_le (a : Γ) (f : WordC0 Γ) : ‖removalC0 a f‖ ≤ ‖f‖ := by
  change ‖(removalC0 a f).toBCF‖ ≤ ‖f‖
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro w
  exact f.toBCF.norm_coe_le_norm (a :: w)

@[simp] theorem removalC0_prefixC0 (a : Γ) (f : WordC0 Γ) :
    removalC0 a (prefixC0 a f) = f := by
  ext w
  simp

@[simp] theorem norm_prefixC0 (a : Γ) (f : WordC0 Γ) : ‖prefixC0 a f‖ = ‖f‖ := by
  apply le_antisymm (norm_prefixC0_le a f)
  simpa only [removalC0_prefixC0] using norm_removalC0_le a (prefixC0 a f)

/-- Prefixing words, bundled as a bounded complex-linear operator. -/
def prefixOperator (a : Γ) : WordC0 Γ →L[ℂ] WordC0 Γ :=
  LinearMap.mkContinuous
    { toFun := prefixC0 a
      map_add' := by
        intro f g
        ext w
        cases w with
        | nil => simp
        | cons b v =>
          by_cases h : b = a <;> simp [h]
      map_smul' := by
        intro c f
        ext w
        cases w with
        | nil => simp
        | cons b v =>
          by_cases h : b = a <;> simp [h] }
    1 (fun f => by simpa using norm_prefixC0_le a f)

/-- Removing the initial letter, bundled as a bounded complex-linear operator. -/
def removalOperator (a : Γ) : WordC0 Γ →L[ℂ] WordC0 Γ :=
  LinearMap.mkContinuous
    { toFun := removalC0 a
      map_add' := by
        intro f g
        ext w
        rfl
      map_smul' := by
        intro c f
        ext w
        rfl }
    1 (fun f => by simpa using norm_removalC0_le a f)

@[simp] theorem prefixOperator_apply (a : Γ) (f : WordC0 Γ) :
    prefixOperator a f = prefixC0 a f := rfl

@[simp] theorem removalOperator_apply (a : Γ) (f : WordC0 Γ) :
    removalOperator a f = removalC0 a f := rfl

theorem norm_prefixOperator_le_one (a : Γ) : ‖prefixOperator a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_prefixC0_le a f

theorem norm_removalOperator_le_one (a : Γ) : ‖removalOperator a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_removalC0_le a f

@[simp] theorem norm_prefixOperator (a : Γ) : ‖prefixOperator a‖ = 1 := by
  apply le_antisymm (norm_prefixOperator_le_one a)
  have h := (prefixOperator a).le_opNorm (wordUnit ([] : List Γ))
  simpa using h

@[simp] theorem removalC0_wordUnit (a : Γ) (w : List Γ) :
    removalC0 a (wordUnit (a :: w)) = wordUnit w := by
  ext v
  simp

@[simp] theorem prefixC0_wordUnit (a : Γ) (w : List Γ) :
    prefixC0 a (wordUnit w) = wordUnit (a :: w) := by
  ext v
  cases v with
  | nil => simp
  | cons b v =>
    by_cases h : b = a
    · subst b
      simp
    · simp [h]

@[simp] theorem norm_removalOperator (a : Γ) : ‖removalOperator a‖ = 1 := by
  apply le_antisymm (norm_removalOperator_le_one a)
  have h := (removalOperator a).le_opNorm (wordUnit (a :: []))
  simpa only [removalOperator_apply, removalC0_wordUnit, norm_wordUnit, mul_one] using h

/-- The source's exact shift relation `Tₐ S_b = δₐb I`. -/
theorem removalOperator_mul_prefixOperator (a b : Γ) :
    removalOperator a * prefixOperator b = if a = b then 1 else 0 := by
  classical
  ext f w
  by_cases h : a = b <;> simp [ContinuousLinearMap.mul_apply, h]

/-- Disjoint cylinders give the finite-column estimate in the source. -/
def wordEvaluation (w : List Γ) : WordC0 Γ →ₗ[ℂ] ℂ where
  toFun f := f w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sum_prefixOperators_apply (F : Finset Γ) (a : Γ → ℂ)
    (f : WordC0 Γ) (w : List Γ) :
    (∑ b ∈ F, a b • prefixOperator b) f w = ∑ b ∈ F, a b * prefixC0 b f w := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    prefixOperator_apply]
  change wordEvaluation w (∑ b ∈ F, a b • prefixC0 b f) = _
  rw [map_sum]
  simp only [map_smul, wordEvaluation, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]

/-- Disjoint cylinders give the finite-column estimate in the source. -/
theorem norm_sum_prefixOperators_le (F : Finset Γ) (a : Γ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ b ∈ F, ‖a b‖ ≤ C) :
    ‖∑ b ∈ F, a b • prefixOperator b‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  change ‖((∑ b ∈ F, a b • prefixOperator b) f).toBCF‖ ≤ C * ‖f‖
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg f))).mpr
  intro w
  change ‖(∑ b ∈ F, a b • prefixOperator b) f w‖ ≤ C * ‖f‖
  rw [sum_prefixOperators_apply]
  cases w with
  | nil => simpa using mul_nonneg hC (norm_nonneg f)
  | cons c v =>
    by_cases hc : c ∈ F
    · have hs : (∑ b ∈ F, a b * prefixC0 b f (c :: v)) = a c * f v := by
        simp [eq_comm, hc]
      rw [hs, norm_mul]
      exact mul_le_mul (ha c hc) (f.toBCF.norm_coe_le_norm v)
        (norm_nonneg _) hC
    · simpa [eq_comm, hc] using mul_nonneg hC (norm_nonneg f)

/-- Every coefficient is also a lower bound, so the column has the supremum norm. -/
theorem norm_coefficient_le_sum_prefixOperators (F : Finset Γ) (a : Γ → ℂ)
    (b : Γ) (hb : b ∈ F) : ‖a b‖ ≤ ‖∑ c ∈ F, a c • prefixOperator c‖ := by
  classical
  let L := ∑ c ∈ F, a c • prefixOperator c
  have heval : L (wordUnit ([] : List Γ)) (b :: []) = a b := by
    dsimp only [L]
    rw [sum_prefixOperators_apply]
    simp [eq_comm, hb]
  have hevalNorm := (L (wordUnit ([] : List Γ))).toBCF.norm_coe_le_norm (b :: [])
  change ‖L (wordUnit ([] : List Γ)) (b :: [])‖ ≤ ‖L (wordUnit ([] : List Γ))‖ at hevalNorm
  have hop := L.le_opNorm (wordUnit ([] : List Γ))
  rw [norm_wordUnit, mul_one] at hop
  exact (show ‖a b‖ ≤ ‖L (wordUnit ([] : List Γ))‖ by
    simpa only [heval] using hevalNorm).trans hop

end SurveyStatements.P2
