import CKEUPFP.Definitions
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Operators from c₀ into a space containing no copy of c₀

The finite-section, phase-alignment, and quantitative block proofs below
are adapted from the user's existing `ThesisCommon` sources. Only the
required declarations have been copied; this file has no external-project
imports and assumes no extraction theorem. The final convergence theorem
uses `ContainsNoCZero` exactly as defined in `Definitions.lean`.
-/

noncomputable section
open Filter Topology
open scoped BigOperators ZeroAtInfty

namespace CKEUPFP
namespace CZeroTools

abbrev CZeroSum (X : Type*) [NormedAddCommGroup X] := C₀(ℕ, X)

section Coordinates
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {ι : Type*} [TopologicalSpace ι]

def cZeroCoordinate (i : ι) : C₀(ι, X) →L[𝕜] X :=
  LinearMap.mkContinuous
    { toFun := fun x => x i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } 1
    (fun x => by simpa using BoundedContinuousFunction.norm_coe_le_norm x.toBCF i)

@[simp] theorem cZeroCoordinate_apply (i : ι) (x : C₀(ι, X)) :
    cZeroCoordinate (𝕜 := 𝕜) i x = x i := rfl

theorem norm_cZeroCoordinate_le (i : ι) : ‖cZeroCoordinate (𝕜 := 𝕜) (X := X) i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _


end Coordinates

section Singles
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]


/-- A vector supported on one natural coordinate is an actual null sequence. -/
def cZeroSingle (i : ℕ) (x : X) : CZeroSum X where
  toFun n := if n = i then x else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    simp [ne_of_gt hn]

@[simp] theorem cZeroSingle_apply (i n : ℕ) (x : X) :
    cZeroSingle i x n = if n = i then x else 0 := rfl

theorem norm_cZeroSingle_le (i : ℕ) (x : X) : ‖cZeroSingle i x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro n
  change ‖if n = i then x else 0‖ ≤ ‖x‖
  split_ifs <;> simp

/-- Bounded coordinate insertion from X to c₀(X). -/
def cZeroSingleCLM (i : ℕ) : X →L[𝕜] CZeroSum X :=
  LinearMap.mkContinuous
    { toFun := cZeroSingle i
      map_add' := by intro x y; ext n; simp; split_ifs <;> simp
      map_smul' := by intro a x; ext n; simp }
    1 (fun x => by simpa using norm_cZeroSingle_le i x)

@[simp] theorem cZeroSingleCLM_apply (i : ℕ) (x : X) :
    cZeroSingleCLM (𝕜 := 𝕜) i x = cZeroSingle i x := rfl


@[simp] theorem norm_cZeroSingle_eq (i : ℕ) (x : X) :
    ‖cZeroSingle i x‖ = ‖x‖ := by
  apply le_antisymm (norm_cZeroSingle_le i x)
  have h := BoundedContinuousFunction.norm_coe_le_norm (cZeroSingle i x).toBCF i
  simpa using h

end Singles

section Insertion
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {ι κ ν : Type*}
variable [TopologicalSpace ι] [DiscreteTopology ι]
variable [TopologicalSpace κ] [DiscreteTopology κ]
variable [TopologicalSpace ν] [DiscreteTopology ν]

/-- Pulling back a null family along an injection preserves vanishing at
infinity and its supremum norm bound. -/
def cZeroRead (e : ι ↪ κ) (x : C₀(κ, X)) : C₀(ι, X) where
  toFun i := x (e i)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    have ht := e.injective.tendsto_cofinite
    rw [← cocompact_eq_cofinite ι, ← cocompact_eq_cofinite κ] at ht
    exact x.zero_at_infty'.comp ht

theorem norm_cZeroRead_le (e : ι ↪ κ) (x : C₀(κ, X)) : ‖cZeroRead e x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro i
  exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF (e i)

/-- Insertion on the image of an injection preserves vanishing at infinity:
every exceptional set is contained in the image of a finite exceptional set. -/
def cZeroInsert (e : ι ↪ κ) (x : C₀(ι, X)) : C₀(κ, X) where
  toFun := Function.extend e x 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    classical
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hx := Metric.tendsto_nhds.mp x.zero_at_infty' ε hε
    rw [cocompact_eq_cofinite] at hx ⊢
    have hbad : {i : ι | ¬ dist (x i) 0 < ε}.Finite := mem_cofinite.mp hx
    filter_upwards [(hbad.image e).compl_mem_cofinite] with k hk
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      rw [e.injective.extend_apply]
      by_contra hi
      exact hk ⟨i, hi, rfl⟩
    · simp [Function.extend_apply' _ _ _ h, hε]

theorem norm_cZeroInsert_le (e : ι ↪ κ) (x : C₀(ι, X)) : ‖cZeroInsert e x‖ ≤ ‖x‖ := by
  classical
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro k
  change ‖Function.extend e x 0 k‖ ≤ ‖x‖
  by_cases h : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := h
    rw [e.injective.extend_apply]
    exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF i
  · simp [Function.extend_apply' _ _ _ h]

def cZeroExtend (e : ι ↪ κ) : C₀(ι, X) →L[𝕜] C₀(κ, X) := by
  classical
  refine LinearMap.mkContinuous
    { toFun := cZeroInsert e
      map_add' := ?_
      map_smul' := ?_ } 1 (fun x => by simpa using norm_cZeroInsert_le e x)
  · intro x y
    ext k
    change Function.extend e (x + y) 0 k = Function.extend e x 0 k + Function.extend e y 0 k
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  · intro a x
    ext k
    change Function.extend e (a • x) 0 k = a • Function.extend e x 0 k
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

@[simp] theorem cZeroExtend_apply_image (e : ι ↪ κ) (x : C₀(ι, X)) (i : ι) :
    cZeroExtend (𝕜 := 𝕜) e x (e i) = x i := by
  simp [cZeroExtend, cZeroInsert, e.injective.extend_apply]

theorem norm_cZeroExtend_le (e : ι ↪ κ) :
    ‖cZeroExtend (𝕜 := 𝕜) (X := X) e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _


@[simp] theorem cZeroExtend_apply_off_range (e : ι ↪ κ) (x : C₀(ι, X))
    {k : κ} (hk : k ∉ Set.range e) : cZeroExtend (𝕜 := 𝕜) e x k = 0 := by
  change Function.extend e x 0 k = 0
  exact Function.extend_apply' (f := e) (fun i => x i) (fun _ : κ => (0 : X)) k hk

theorem cZeroExtend_read_eq (e : ι ↪ κ) (x : C₀(κ, X))
    (hx : ∀ k, k ∉ Set.range e → x k = 0) :
    cZeroExtend (𝕜 := 𝕜) e (cZeroRead e x) = x := by
  classical
  ext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    rw [cZeroExtend_apply_image]
    rfl
  · rw [cZeroExtend_apply_off_range e _ hk, hx k hk]

/-- Composition of zero insertions for actual null families. -/
theorem cZeroExtend_comp (e : ι ↪ κ) (f : κ ↪ ν) :
    (cZeroExtend (𝕜 := 𝕜) (X := X) f).comp (cZeroExtend e) = cZeroExtend (e.trans f) := by
  ext x k
  change Function.extend f (Function.extend e x 0) 0 k = Function.extend (f ∘ e) x 0 k
  exact congrFun (e.injective.extend_comp f.injective x 0).symm k


end Insertion

section ScalarSingles
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]


theorem cZeroExtend_single (e : ℕ ↪ ℕ) (n : ℕ) (x : X) :
    cZeroExtend (𝕜 := 𝕜) e (cZeroSingle n x) = cZeroSingle (e n) x := by
  ext m
  by_cases hm : m ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hm
    rw [cZeroExtend_apply_image]
    simp only [cZeroSingle_apply, e.injective.eq_iff]
  · have hmn : m ≠ e n := fun heq => hm ⟨n, heq.symm⟩
    simp only [cZeroExtend_apply_off_range e _ hm, cZeroSingle_apply, if_neg hmn]


theorem cZero_finite_singles_apply (F : Finset ℕ) (a : ℕ → 𝕜) (i : ℕ) :
    (∑ n ∈ F, a n • cZeroSingle n (1 : 𝕜)) i = if i ∈ F then a i else 0 := by
  classical
  change cZeroCoordinate (𝕜 := 𝕜) i (∑ n ∈ F, a n • cZeroSingle n (1 : 𝕜)) = _
  simp [map_sum, map_smul, cZeroSingle_apply, Finset.sum_ite_eq]

/-- Ordered finite sections converge in the supremum norm because the vector
itself tends to zero; coordinatewise convergence alone is not used. -/
theorem cZero_finite_singles_tendsto (x : CZeroSum 𝕜) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, x n • cZeroSingle n (1 : 𝕜))
      atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hx : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop, norm_zero]
      using x.zero_at_infty'.norm
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hx).2 (ε / 2) (half_pos hε))
  refine ⟨N, fun M hM => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro i
  change ‖(∑ n ∈ Finset.range M, x n • cZeroSingle n (1 : 𝕜)) i - x i‖ ≤ ε / 2
  rw [cZero_finite_singles_apply]
  by_cases hi : i ∈ Finset.range M
  · simpa only [if_pos hi, sub_self, norm_zero] using (half_pos hε).le
  · simp only [hi, if_false, zero_sub, norm_neg]
    exact (hN i (hM.trans (Nat.le_of_not_lt (by simpa using hi)))).le


end ScalarSingles

section ColumnOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

def CZeroFiniteColumnBound (F : ℕ → X →L[𝕜] Y) (C : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → X) (b : ℝ), 0 ≤ b →
    (∀ i ∈ s, ‖x i‖ ≤ b) → ‖∑ i ∈ s, F i (x i)‖ ≤ C*b

theorem cZero_columns_summable (F : ℕ → X →L[𝕜] Y) {C : ℝ}
    (hC : 0 ≤ C) (hF : CZeroFiniteColumnBound F C) (x : CZeroSum X) :
    Summable (fun i => F i (x i)) := by
  classical
  apply summable_iff_vanishing_norm.2
  intro ε hε
  let η := ε/(C+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hsmall : C*η < ε := by
    dsimp [η]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C+1)]
    nlinarith
  have hx : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop, norm_zero] using x.zero_at_infty'.norm
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hx).2 η hη)
  refine ⟨Finset.range N, ?_⟩
  intro s hs
  apply (hF s x η hη.le ?_).trans_lt hsmall
  intro i hi
  apply (hN i ?_).le
  by_contra h
  exact Finset.disjoint_left.1 hs hi (Finset.mem_range.mpr (by omega))

theorem norm_cZero_columns_tsum_le (F : ℕ → X →L[𝕜] Y) {C : ℝ}
    (hC : 0 ≤ C) (hF : CZeroFiniteColumnBound F C) (x : CZeroSum X) :
    ‖∑' i, F i (x i)‖ ≤ C*‖x‖ := by
  apply le_of_tendsto (cZero_columns_summable F hC hF x).hasSum.norm
  exact Eventually.of_forall (fun s => hF s x ‖x‖ (norm_nonneg x)
    (fun i _ => BoundedContinuousFunction.norm_coe_le_norm x.toBCF i))

def cZeroColumns (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC : 0 ≤ C)
    (hF : CZeroFiniteColumnBound F C) : CZeroSum X →L[𝕜] Y :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, F i (x i)
      map_add' := by
        intro x y
        change (∑' i, F i (x i+y i)) = _
        simp only [map_add]
        exact (cZero_columns_summable F hC hF x).tsum_add (cZero_columns_summable F hC hF y)
      map_smul' := by
        intro a x
        change (∑' i, F i (a • x i)) = _
        simp only [map_smul]
        exact (cZero_columns_summable F hC hF x).tsum_const_smul a }
    C (norm_cZero_columns_tsum_le F hC hF)

theorem norm_cZeroColumns_le (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC hF) :
    ‖cZeroColumns F C hC hF‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

theorem cZeroColumns_single (F : ℕ → X →L[𝕜] Y) (C : ℝ) (hC hF) (j : ℕ) (x : X) :
    cZeroColumns F C hC hF (cZeroSingle j x) = F j x := by
  change (∑' i, F i (cZeroSingle j x i)) = _
  rw [tsum_eq_single j]
  · simp
  · intro i hij
    simp [hij]


end ColumnOperators

section ScalarRows
variable {𝕜 : Type*} [RCLike 𝕜]


/-- Align phases before applying the functional; this works over R or C. -/
theorem sum_norm_apply_le_of_unit_sums {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (φ : E →L[𝕜] 𝕜)
    (x : ℕ → E) (K : ℝ)
    (h : ∀ (F : Finset ℕ) (a : ℕ → 𝕜), (∀ n ∈ F, ‖a n‖ ≤ 1) →
      ‖∑ n ∈ F, a n • x n‖ ≤ K) (F : Finset ℕ) :
    ∑ n ∈ F, ‖φ (x n)‖ ≤ ‖φ‖ * K := by
  choose a ha hphase using fun n => RCLike.exists_norm_eq_mul_self (φ (x n))
  have heq : φ (∑ n ∈ F, a n • x n) = ((∑ n ∈ F, ‖φ (x n)‖ : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun n _ => (hphase n).symm)
  calc
    _ = ‖φ (∑ n ∈ F, a n • x n)‖ := by
      rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖φ‖ * ‖∑ n ∈ F, a n • x n‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * K := mul_le_mul_of_nonneg_left (h F a (fun n _ => (ha n).le)) (norm_nonneg _)


theorem cZero_functional_row_sum_le (φ : CZeroSum 𝕜 →L[𝕜] 𝕜) (F : Finset ℕ) :
    ∑ n ∈ F, ‖φ (cZeroSingle n 1)‖ ≤ ‖φ‖ := by
  apply (sum_norm_apply_le_of_unit_sums φ (fun n => cZeroSingle n 1) 1 ?_ F).trans_eq
    (mul_one _)
  intro G a ha
  apply (BoundedContinuousFunction.norm_le zero_le_one).2
  intro i
  change ‖(∑ n ∈ G, a n • cZeroSingle n (1 : 𝕜)) i‖ ≤ 1
  rw [cZero_finite_singles_apply]
  split_ifs with hi
  · exact ha i hi
  · simp

theorem cZero_functional_row_summable (φ : CZeroSum 𝕜 →L[𝕜] 𝕜) :
    Summable (fun n => ‖φ (cZeroSingle n 1)‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (cZero_functional_row_sum_le φ)

theorem cZero_functional_norm_eq_tsum (φ : CZeroSum 𝕜 →L[𝕜] 𝕜) :
    ‖φ‖ = ∑' n, ‖φ (cZeroSingle n 1)‖ := by
  have hs := cZero_functional_row_summable φ
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg (fun _ => norm_nonneg _))
    intro x
    apply le_of_tendsto ((φ.continuous.tendsto x).comp
      (cZero_finite_singles_tendsto x)).norm
    apply Eventually.of_forall
    intro N
    change ‖φ (∑ n ∈ Finset.range N, x n • cZeroSingle n (1 : 𝕜))‖ ≤ _
    simp only [map_sum, map_smul]
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖x n‖ * ‖φ (cZeroSingle n 1)‖ := by
        simpa only [norm_smul] using norm_sum_le (Finset.range N)
          (fun n => x n • φ (cZeroSingle n 1))
      _ ≤ ∑ n ∈ Finset.range N, ‖x‖ * ‖φ (cZeroSingle n 1)‖ :=
        Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right
          (BoundedContinuousFunction.norm_coe_le_norm x.toBCF n) (norm_nonneg _))
      _ ≤ ‖x‖ * ∑' n, ‖φ (cZeroSingle n 1)‖ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (hs.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _)) (norm_nonneg x)
      _ = _ := mul_comm _ _
  · exact hs.tsum_le_of_sum_le (cZero_functional_row_sum_le φ)

theorem cZero_functional_near_coordinate (φ : CZeroSum 𝕜 →L[𝕜] 𝕜)
    (n : ℕ) {d δ : ℝ} (hφ : ‖φ‖ ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hdiag : φ (cZeroSingle n 1) = (d : 𝕜)) (hδ : 1 - δ ≤ d) :
    ‖φ - (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n)‖ ≤ 2 * δ := by
  classical
  have hn : ‖φ (cZeroSingle n 1)‖ = d := by
    rw [hdiag, RCLike.norm_ofReal, abs_of_nonneg hd]
  have hr : ‖(φ - (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n)) (cZeroSingle n 1)‖ = 1 - d := by
    simp only [ContinuousLinearMap.sub_apply, cZeroCoordinate_apply, cZeroSingle_apply,
      ite_true, hdiag]
    rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal,
      abs_of_nonpos (sub_nonpos.mpr hd1)]
    ring
  have hrest : (fun i => if i = n then 0 else ‖(φ - (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n)) (cZeroSingle i 1)‖) =
      (fun i => if i = n then 0 else ‖φ (cZeroSingle i 1)‖) := by
    funext i
    split_ifs with hi
    · rfl
    · simp [ContinuousLinearMap.sub_apply, cZeroSingle_apply, Ne.symm hi]
  rw [cZero_functional_norm_eq_tsum,
    (cZero_functional_row_summable (φ - (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n))).tsum_eq_add_tsum_ite n,
    hr, hrest]
  have hsum := cZero_functional_norm_eq_tsum φ
  rw [(cZero_functional_row_summable φ).tsum_eq_add_tsum_ite n, hn] at hsum
  linarith


end ScalarRows

section SubcopyExtraction
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]


def cZeroTailEmbedding (p : ℕ) : ℕ ↪ ℕ := ⟨fun n => p+n, by intro i j hij; dsimp at hij; omega⟩

theorem exists_cZero_finite_tail_norming_vector
    (V : CZeroSum 𝕜 →L[𝕜] E) (p : ℕ) {r : ℝ}
    (hr : r < ‖V.comp (cZeroExtend (cZeroTailEmbedding p))‖) :
    ∃ q : ℕ, ∃ x : CZeroSum 𝕜, p < q ∧ ‖x‖ ≤ 1 ∧
      (∀ i, i < p ∨ q ≤ i → x i = 0) ∧ r < ‖V x‖ := by
  classical
  let J := cZeroExtend (𝕜 := 𝕜) (X := 𝕜) (cZeroTailEmbedding p)
  obtain ⟨y, hy, hVy⟩ := (V.comp J).exists_lt_apply_of_lt_opNorm hr
  let z (N : ℕ) := ∑ n ∈ Finset.range N, y n • cZeroSingle n (1 : 𝕜)
  have ht : Tendsto (fun N => ‖V (J (z N))‖) atTop (𝓝 ‖V (J y)‖) :=
    ((V.continuous.comp J.continuous).tendsto y |>.comp (cZero_finite_singles_tendsto y)).norm
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (Ioi_mem_nhds hVy))
  have hz : ‖z N‖ ≤ ‖y‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg y)).2
    intro i
    change ‖(∑ n ∈ Finset.range N, y n • cZeroSingle n (1 : 𝕜)) i‖ ≤ ‖y‖
    rw [cZero_finite_singles_apply]
    split_ifs
    · exact BoundedContinuousFunction.norm_coe_le_norm y.toBCF i
    · simp
  refine ⟨p+N+1, J (z N), by omega, ?_, ?_, hN N le_rfl⟩
  · exact (norm_cZeroInsert_le (cZeroTailEmbedding p) (z N)).trans (hz.trans hy.le)
  · intro i hi
    change Function.extend (cZeroTailEmbedding p) (z N) 0 i = 0
    by_cases hpi : p ≤ i
    · have heq : cZeroTailEmbedding p (i-p) = i := by dsimp [cZeroTailEmbedding]; omega
      rw [← heq, Function.Injective.extend_apply (cZeroTailEmbedding p).injective]
      change (∑ n ∈ Finset.range N, y n • cZeroSingle n (1 : 𝕜)) (i-p) = 0
      rw [cZero_finite_singles_apply, if_neg]
      simp only [Finset.mem_range]
      omega
    · apply Function.extend_apply' _ _ _
      rintro ⟨j, hj⟩
      change p+j=i at hj
      omega

theorem exists_cZero_successive_norming_blocks (V : CZeroSum 𝕜 →L[𝕜] E) {r : ℝ}
    (hr : ∀ p, r < ‖V.comp (cZeroExtend (cZeroTailEmbedding p))‖) :
    ∃ x : ℕ → CZeroSum 𝕜, (∀ n, ‖x n‖ ≤ 1) ∧
      (∀ i j, i ≠ j → ∀ k, x i k = 0 ∨ x j k = 0) ∧
      ∀ n, r < ‖V (x n)‖ := by
  classical
  choose q x hq hx hs hV using fun p => exists_cZero_finite_tail_norming_vector V p (hr p)
  let p : ℕ → ℕ := fun n => q^[n] 0
  have hp : ∀ n, p (n+1) = q (p n) := fun n => Function.iterate_succ_apply' q n 0
  have hpm : StrictMono p := strictMono_nat_of_lt_succ (fun n => by rw [hp]; exact hq _)
  refine ⟨fun n => x (p n), fun n => hx _, ?_, fun n => hV _⟩
  intro i j hij k
  rcases lt_or_gt_of_ne hij with hij | hji
  · by_cases hk : k < q (p i)
    · right
      apply hs (p j) k
      left
      have hle := hpm.monotone (Nat.succ_le_of_lt hij)
      rw [hp] at hle
      omega
    · exact Or.inl (hs (p i) k (Or.inr (le_of_not_gt hk)))
  · by_cases hk : k < q (p j)
    · left
      apply hs (p i) k
      left
      have hle := hpm.monotone (Nat.succ_le_of_lt hji)
      rw [hp] at hle
      omega
    · exact Or.inr (hs (p j) k (Or.inr (le_of_not_gt hk)))

theorem cZero_disjoint_finiteColumnBound (x : ℕ → CZeroSum 𝕜)
    (hx : ∀ n, ‖x n‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ k, x i k = 0 ∨ x j k = 0) :
    CZeroFiniteColumnBound
      (fun n => (ContinuousLinearMap.id 𝕜 𝕜).smulRight (x n)) 1 := by
  classical
  intro s a b hb ha
  simp only [one_mul]
  apply (BoundedContinuousFunction.norm_le hb).2
  intro k
  change ‖cZeroCoordinate (𝕜 := 𝕜) k
    (∑ n ∈ s, (ContinuousLinearMap.id 𝕜 𝕜).smulRight (x n) (a n))‖ ≤ b
  simp only [map_sum, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    map_smul, cZeroCoordinate_apply, smul_eq_mul]
  by_cases hh : ∃ i ∈ s, x i k ≠ 0
  · obtain ⟨i, hi, hne⟩ := hh
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [norm_mul]
      exact (mul_le_mul (ha i hi)
        ((BoundedContinuousFunction.norm_coe_le_norm (x i).toBCF k).trans (hx i))
        (norm_nonneg _) hb).trans_eq (mul_one b)
    · intro j hj hji
      rw [(hdis i j hji.symm k).resolve_left hne, mul_zero]
  · push_neg at hh
    rw [Finset.sum_eq_zero (fun i hi => by rw [hh i hi, mul_zero]), norm_zero]
    exact hb

theorem exists_cZero_norming_block_operator (V : CZeroSum 𝕜 →L[𝕜] E) {r : ℝ}
    (hr : ∀ p, r < ‖V.comp (cZeroExtend (cZeroTailEmbedding p))‖) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ‖A‖ ≤ 1 ∧
      ∀ n, r < ‖V (A (cZeroSingle n 1))‖ := by
  obtain ⟨x, hx, hdis, hV⟩ := exists_cZero_successive_norming_blocks V hr
  let F (n : ℕ) := (ContinuousLinearMap.id 𝕜 𝕜).smulRight (x n)
  let A := cZeroColumns F 1 zero_le_one (cZero_disjoint_finiteColumnBound x hx hdis)
  refine ⟨A, norm_cZeroColumns_le .., ?_⟩
  intro n
  have heq : A (cZeroSingle n 1) = x n := by
    rw [show A = cZeroColumns F 1 zero_le_one (cZero_disjoint_finiteColumnBound x hx hdis) from rfl,
      cZeroColumns_single]
    simp [F]
  rw [heq]
  exact hV n


theorem exists_cZero_almost_maximal_blocks_of_tail_lower_bound (V : CZeroSum 𝕜 →L[𝕜] E)
    {c δ : ℝ} (hc : 0 < c)
    (htail : ∀ n, c ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding n))‖)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ∃ b : ℝ,
      c ≤ b ∧ ‖A‖ ≤ 1 ∧ ‖V.comp A‖ ≤ b ∧
      ∀ n, (1-δ)*b < ‖V (A (cZeroSingle n 1))‖ := by
  classical
  let J (n : ℕ) := cZeroExtend (𝕜 := 𝕜) (X := 𝕜) (cZeroTailEmbedding n)
  let f (n : ℕ) := ‖V.comp (J n)‖
  have hcf (n : ℕ) : c ≤ f n := htail n
  let b₀ := sInf (Set.range f)
  have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨n, rfl⟩; exact hcf n⟩
  have hcb₀ : c ≤ b₀ := le_csInf (Set.range_nonempty f) (by rintro _ ⟨n, rfl⟩; exact hcf n)
  have hb₀pos : 0 < b₀ := hc.trans_le hcb₀
  have hb₀f (n : ℕ) : b₀ ≤ f n := csInf_le hbdd ⟨n, rfl⟩
  have hbigger : b₀ < b₀/(1-δ) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1-δ)]
    nlinarith
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_csInf_lt (Set.range_nonempty f) hbigger
  let W := V.comp (J N)
  have hr : (1-δ)*f N < b₀ := by
    have h := (lt_div_iff₀ (by linarith : 0 < 1-δ)).1 hN
    nlinarith
  have htail (p : ℕ) : W.comp (cZeroExtend (cZeroTailEmbedding p)) = V.comp (J (N+p)) := by
    change (V.comp (cZeroExtend (cZeroTailEmbedding N))).comp
      (cZeroExtend (cZeroTailEmbedding p)) = _
    rw [ContinuousLinearMap.comp_assoc, cZeroExtend_comp]
    congr 1
    congr 1
    ext n
    simp [cZeroTailEmbedding, Nat.add_assoc]
  obtain ⟨A, hA, hcol⟩ := exists_cZero_norming_block_operator W
    (fun p => by rw [htail]; exact hr.trans_le (hb₀f (N+p)))
  refine ⟨(J N).comp A, f N, hcf N, ?_, ?_, hcol⟩
  · exact ((J N).opNorm_comp_le A).trans
      ((mul_le_mul (norm_cZeroExtend_le (cZeroTailEmbedding N)) hA
        (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))
  · rw [← ContinuousLinearMap.comp_assoc]
    exact (W.opNorm_comp_le A).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hA (norm_nonneg W))


theorem cZero_lower_bound_of_near_unit_columns
    (V : CZeroSum 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcol : ∀ n, 1-δ ≤ ‖V (cZeroSingle n 1)‖) (x : CZeroSum 𝕜) :
    (1-2*δ)*‖x‖ ≤ ‖V x‖ := by
  classical
  choose φ hφ hφnorm using fun n => exists_dual_vector'' 𝕜 (V (cZeroSingle n 1))
  have hrow (n : ℕ) : ‖(φ n).comp V - cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n‖ ≤ 2*δ := by
    apply cZero_functional_near_coordinate _ n
      (((φ n).opNorm_comp_le V).trans
        ((mul_le_mul (hφ n) hV (norm_nonneg V) zero_le_one).trans_eq (one_mul 1)))
      (norm_nonneg _) _ (hφnorm n) (hcol n)
    exact (V.le_opNorm _).trans
      ((mul_le_mul hV (norm_cZeroSingle_le n (1 : 𝕜))
        (norm_nonneg _) zero_le_one).trans (by simp))
  have hb : ‖x‖ ≤ ‖V x‖+2*δ*‖x‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro n
    have he : ‖φ n (V x) - x n‖ ≤ 2*δ*‖x‖ :=
      (((φ n).comp V - cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hrow n) (norm_nonneg x))
    have hv : ‖φ n (V x)‖ ≤ ‖V x‖ := ((φ n).le_opNorm _).trans
      (by simpa using mul_le_mul_of_nonneg_right (hφ n) (norm_nonneg (V x)))
    have hh := norm_sub_le (φ n (V x)) (φ n (V x)-x n)
    rw [sub_sub_cancel] at hh
    exact hh.trans (add_le_add hv he)
  nlinarith

theorem exists_cZero_subcopy_of_tail_lower_bound (V : CZeroSum 𝕜 →L[𝕜] E)
    {c δ : ℝ} (hc : 0 < c)
    (htail : ∀ n, c ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding n))‖)
    (hδ : 0 < δ) (hδsmall : 2*δ < 1) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ‖A‖ ≤ 1 ∧
      ∀ x, ((1-2*δ)*c)*‖x‖ ≤ ‖V (A x)‖ := by
  letI : NormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] E) :=
    @NormedSpace.toNormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] E) _ _ _
  obtain ⟨A, b, hcb, hA, hVA, hcol⟩ :=
    exists_cZero_almost_maximal_blocks_of_tail_lower_bound V hc htail hδ (by linarith)
  have hb : 0 < b := hc.trans_le hcb
  let U : CZeroSum 𝕜 →L[𝕜] E := ((b⁻¹ : ℝ) : 𝕜) • (V.comp A)
  have hU : ‖U‖ ≤ 1 := by
    dsimp [U]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    exact (mul_le_mul_of_nonneg_left hVA (inv_nonneg.mpr hb.le)).trans_eq
      (inv_mul_cancel₀ hb.ne')
  have hUc (n : ℕ) : 1-δ ≤ ‖U (cZeroSingle n 1)‖ := by
    change 1-δ ≤ ‖((b⁻¹ : ℝ) : 𝕜) • V (A (cZeroSingle n 1))‖
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    have h := mul_le_mul_of_nonneg_left (hcol n).le (inv_nonneg.mpr hb.le)
    have heq : b⁻¹ * ((1-δ)*b) = 1-δ := by field_simp
    exact heq.symm.trans_le h
  refine ⟨A, hA, ?_⟩
  intro x
  have h := cZero_lower_bound_of_near_unit_columns U hU hδ.le hUc x
  change (1-2*δ)*‖x‖ ≤ ‖((b⁻¹ : ℝ) : 𝕜) • V (A x)‖ at h
  rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)] at h
  have hh := mul_le_mul_of_nonneg_left h hb.le
  rw [← mul_assoc b b⁻¹, mul_inv_cancel₀ hb.ne', one_mul] at hh
  have hcb' := mul_le_mul_of_nonneg_right hcb
    (mul_nonneg (by linarith : 0 ≤ 1-2*δ) (norm_nonneg x))
  nlinarith


end SubcopyExtraction

end CZeroTools

open CZeroTools

section NoCZeroConsequences
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If a positive bound persists on every tail of an operator from c₀,
the quantitative block construction gives a forbidden copy of c₀. -/
theorem exists_cZero_tail_small (hE : ContainsNoCZero 𝕜 E)
    (V : CZero 𝕜 →L[𝕜] E) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ‖V.comp (cZeroExtend (cZeroTailEmbedding N))‖ < ε := by
  by_contra h
  have htail : ∀ N : ℕ, ε ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding N))‖ := by
    simpa only [not_exists, not_lt] using h
  obtain ⟨A, _, hlow⟩ := exists_cZero_subcopy_of_tail_lower_bound V hε htail
    (δ := 1 / 4) (by norm_num) (by norm_num)
  apply hE
  refine ⟨V.comp A, ε / 2, by positivity, ?_⟩
  intro x
  convert hlow x using 1
  ring

/-- A coordinate vector beyond the Nth coordinate is the insertion of a
unit vector from the Nth tail, so its image is bounded by the tail norm. -/
theorem cZero_column_norm_le_tail (V : CZero 𝕜 →L[𝕜] E)
    (N k : ℕ) (hk : N ≤ k) :
    ‖V (cZeroSingle k 1)‖ ≤
      ‖V.comp (cZeroExtend (cZeroTailEmbedding N))‖ := by
  have heq : cZeroExtend (𝕜 := 𝕜) (cZeroTailEmbedding N)
      (cZeroSingle (k - N) (1 : 𝕜)) = cZeroSingle k (1 : 𝕜) := by
    rw [cZeroExtend_single]
    congr 1
    simp only [cZeroTailEmbedding, Function.Embedding.coeFn_mk]
    omega
  have h := (V.comp (cZeroExtend (cZeroTailEmbedding N))).le_opNorm
    (cZeroSingle (k - N) (1 : 𝕜))
  simpa only [ContinuousLinearMap.comp_apply, heq, norm_cZeroSingle_eq,
    norm_one, mul_one] using h

/-- Tail norms decrease when more initial coordinates are removed. -/
theorem cZero_tail_norm_mono (V : CZero 𝕜 →L[𝕜] E)
    (N k : ℕ) (hk : N ≤ k) :
    ‖V.comp (cZeroExtend (cZeroTailEmbedding k))‖ ≤
      ‖V.comp (cZeroExtend (cZeroTailEmbedding N))‖ := by
  have hJ : (cZeroExtend (𝕜 := 𝕜) (X := 𝕜) (cZeroTailEmbedding N)).comp
      (cZeroExtend (cZeroTailEmbedding (k - N))) =
        cZeroExtend (cZeroTailEmbedding k) := by
    rw [cZeroExtend_comp]
    congr 1
    ext n
    change N + (k - N + n) = k + n
    omega
  calc
    _ = ‖(V.comp (cZeroExtend (cZeroTailEmbedding N))).comp
          (cZeroExtend (cZeroTailEmbedding (k - N)))‖ := by
      rw [ContinuousLinearMap.comp_assoc, hJ]
    _ ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding N))‖ *
          ‖cZeroExtend (𝕜 := 𝕜) (X := 𝕜) (cZeroTailEmbedding (k - N))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding N))‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_cZeroExtend_le _)
        (ContinuousLinearMap.opNorm_nonneg _)
    _ = _ := mul_one _

/-- The tail operator norms tend to zero, a stronger conclusion than
convergence of the coordinate columns. -/
theorem noCZero_tail_norms_tendsto_zero (hE : ContainsNoCZero 𝕜 E)
    (V : CZero 𝕜 →L[𝕜] E) :
    Tendsto (fun n => ‖V.comp (cZeroExtend (cZeroTailEmbedding n))‖)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_cZero_tail_small hE V hε
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [Real.dist_eq, sub_zero,
    abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _)] using
    (cZero_tail_norm_mono V N n hn).trans_lt hN

/-- Every bounded operator from c₀ into a space containing no isomorphic
copy of c₀ sends the standard unit vectors to vectors converging to zero.
The hypothesis is precisely the paper's `ContainsNoCZero` condition. -/
theorem noCZero_columns_tendsto_zero (hE : ContainsNoCZero 𝕜 E)
    (V : CZero 𝕜 →L[𝕜] E) :
    Tendsto (fun n => ‖V (cZeroSingle n 1)‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_cZero_tail_small hE V hε
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using
    (cZero_column_norm_le_tail V N n hn).trans_lt hN

/-- The coordinate images form an unconditionally convergent series. This
is stronger than merely asserting that its terms converge to zero. -/
theorem noCZero_unit_columns_summable [CompleteSpace E]
    (hE : ContainsNoCZero 𝕜 E) (V : CZero 𝕜 →L[𝕜] E) :
    Summable (fun n => V (cZeroSingle n 1)) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_cZero_tail_small hE V hε
  refine ⟨Finset.range N, ?_⟩
  intro s hs
  let x : CZero 𝕜 := ∑ i ∈ s, (1 : 𝕜) • cZeroSingle i 1
  have hxnorm : ‖x‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro k
    change ‖(∑ i ∈ s, (1 : 𝕜) • cZeroSingle i 1) k‖ ≤ 1
    rw [cZero_finite_singles_apply]
    split_ifs <;> simp
  have hzero : ∀ k, k ∉ Set.range (cZeroTailEmbedding N) → x k = 0 := by
    intro k hk
    have hkn : k < N := by
      by_contra hn
      apply hk
      refine ⟨k - N, ?_⟩
      change N + (k - N) = k
      omega
    have hks : k ∉ s := by
      intro hks
      exact Finset.disjoint_left.mp hs hks (Finset.mem_range.mpr hkn)
    dsimp only [x]
    rw [cZero_finite_singles_apply, if_neg hks]
  have hxrepr := cZeroExtend_read_eq (𝕜 := 𝕜) (cZeroTailEmbedding N) x hzero
  calc
    ‖∑ i ∈ s, V (cZeroSingle i 1)‖ = ‖V x‖ := by simp [x, map_sum]
    _ = ‖(V.comp (cZeroExtend (cZeroTailEmbedding N)))
          (cZeroRead (cZeroTailEmbedding N) x)‖ := by
      rw [ContinuousLinearMap.comp_apply, hxrepr]
    _ ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding N))‖ *
          ‖cZeroRead (cZeroTailEmbedding N) x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding N))‖ * 1 :=
      mul_le_mul_of_nonneg_left ((norm_cZeroRead_le _ x).trans hxnorm)
        (ContinuousLinearMap.opNorm_nonneg _)
    _ < ε := by simpa only [mul_one] using hN

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Pairwise disjoint continuous functions admit a bounded scalar c₀
synthesis map. This is the direct substitute for disjoint-set semivariation. -/
theorem disjoint_continuous_finiteColumnBound (f : ℕ → C(K, E))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n, ‖f n‖ ≤ B)
    (hdis : ∀ i j, i ≠ j → ∀ t, f i t = 0 ∨ f j t = 0) :
    CZeroFiniteColumnBound
      (fun n => (ContinuousLinearMap.id 𝕜 𝕜).smulRight (f n)) B := by
  classical
  intro s a b hb ha
  apply (ContinuousMap.norm_le _ (mul_nonneg hB hb)).mpr
  intro t
  change ‖(ContinuousMap.evalCLM 𝕜 t)
    (∑ n ∈ s, (ContinuousLinearMap.id 𝕜 𝕜).smulRight (f n) (a n))‖ ≤ B * b
  rw [map_sum]
  simp only [ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, map_smul]
  change ‖∑ n ∈ s, a n • f n t‖ ≤ B * b
  by_cases hh : ∃ i ∈ s, f i t ≠ 0
  · obtain ⟨i, hi, hne⟩ := hh
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [norm_smul]
      exact (mul_le_mul (ha i hi) ((f i).norm_coe_le_norm t |>.trans (hf i))
        (norm_nonneg _) hb).trans_eq (mul_comm b B)
    · intro j _ hji
      rw [(hdis i j hji.symm t).resolve_left hne, smul_zero]
  · push_neg at hh
    rw [Finset.sum_eq_zero (fun i hi => by rw [hh i hi, smul_zero]), norm_zero]
    exact mul_nonneg hB hb

variable [CompleteSpace E]

/-- Every bounded row into a no-c₀ space tends to zero on a uniformly
bounded sequence of functions with pairwise disjoint supports. The result
is proved by an actual c₀ synthesis operator, with no vector measures. -/
theorem noCZero_disjoint_rows_tendsto_zero (hE : ContainsNoCZero 𝕜 E)
    (R : C(K, E) →L[𝕜] E) (f : ℕ → C(K, E))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n, ‖f n‖ ≤ B)
    (hdis : ∀ i j, i ≠ j → ∀ t, f i t = 0 ∨ f j t = 0) :
    Tendsto (fun n => ‖R (f n)‖) atTop (𝓝 0) := by
  let F (n : ℕ) := (ContinuousLinearMap.id 𝕜 𝕜).smulRight (f n)
  have hbound : CZeroFiniteColumnBound F B :=
    disjoint_continuous_finiteColumnBound f hB hf hdis
  have ht := noCZero_columns_tendsto_zero hE (R.comp (cZeroColumns F B hB hbound))
  simpa only [ContinuousLinearMap.comp_apply, cZeroColumns_single, F,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    one_smul] using ht

/-- The full unconditional convergence assertion for rows on disjoint
functions. It will give diagonal-atom limits on shrinking Cantor cylinders. -/
theorem noCZero_disjoint_rows_summable (hE : ContainsNoCZero 𝕜 E)
    (R : C(K, E) →L[𝕜] E) (f : ℕ → C(K, E))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n, ‖f n‖ ≤ B)
    (hdis : ∀ i j, i ≠ j → ∀ t, f i t = 0 ∨ f j t = 0) :
    Summable (fun n => R (f n)) := by
  let F (n : ℕ) := (ContinuousLinearMap.id 𝕜 𝕜).smulRight (f n)
  have hbound : CZeroFiniteColumnBound F B :=
    disjoint_continuous_finiteColumnBound f hB hf hdis
  have hs := noCZero_unit_columns_summable hE (R.comp (cZeroColumns F B hB hbound))
  simpa only [ContinuousLinearMap.comp_apply, cZeroColumns_single, F,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    one_smul] using hs

end NoCZeroConsequences
end CKEUPFP
