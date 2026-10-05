import Posets.WolfePreservationNecessaryAtomic

/-! Continuous images of source clopen blocks retain more information than
arbitrary disjoint atomic sets. They have a pointwise ℓ¹ budget, and the
lifted measures pair with them as exact scaled characteristic functions. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Filter Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace L]

def wolfeSourceBlock (V : Set L) (hV : IsClopen V) : JLMS.CZero 𝕜 L :=
  JLMS.clopenIndicator V hV hV.isClosed.isCompact

@[simp] theorem wolfeSourceBlock_apply (V : Set L) (hV : IsClopen V) (x : L) :
    wolfeSourceBlock (𝕜 := 𝕜) V hV x = if x ∈ V then 1 else 0 :=
  JLMS.clopenIndicator_apply _ _ _ _

theorem wolfeSourceBlock_norm_le (V : Set L) (hV : IsClopen V) :
    ‖wolfeSourceBlock (𝕜 := 𝕜) V hV‖ ≤ 1 := JLMS.norm_clopenIndicator_le _ _ _

theorem wolfeSourceBlock_support (V : Set L) (hV : IsClopen V) :
    Function.support (wolfeSourceBlock (𝕜 := 𝕜) V hV) = V := by
  ext x
  simp only [Function.mem_support, wolfeSourceBlock_apply]
  by_cases hx : x ∈ V <;> simp [hx]

def wolfeBlockImage (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (V : Set L) (hV : IsClopen V) : JLMS.CZero 𝕜 K := S (wolfeSourceBlock V hV)

theorem wolfeBlockImage_norm_le (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (V : Set L) (hV : IsClopen V) : ‖wolfeBlockImage S V hV‖ ≤ ‖S‖ :=
  (S.le_opNorm _).trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (wolfeSourceBlock_norm_le (𝕜 := 𝕜) V hV) (norm_nonneg S))

theorem wolfeBlockImage_apply_le (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (V : Set L) (hV : IsClopen V) (y : K) : ‖wolfeBlockImage S V hV y‖ ≤ ‖S‖ :=
  (JLMS.norm_CZero_apply_le _ y).trans (wolfeBlockImage_norm_le S V hV)

theorem wolfeBlockImage_finite_budget (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (hd : Pairwise fun n m => Disjoint (V n) (V m)) (s : Finset ℕ) (y : K) :
    ∑ n ∈ s, ‖wolfeBlockImage S (V n) (hV n) y‖ ≤ ‖S‖ := by
  let η (n : ℕ) := wolfeSourceBlock (𝕜 := 𝕜) (V n) (hV n)
  have hu (n : ℕ) : ‖η n‖ ≤ 1 := wolfeSourceBlock_norm_le _ _
  have hη : Pairwise fun n m => Disjoint (Function.support (η n)) (Function.support (η m)) := by
    intro n m hnm
    simpa only [η, wolfeSourceBlock_support] using hd hnm
  let A := JLMS.disjointSynthesis η hu hη
  let φ := (JLMS.evaluation (𝕜 := 𝕜) y).comp (S.comp A)
  have h := JLMS.cZero_dual_finite_coordinate_mass φ s
  have hφ : ‖φ‖ ≤ ‖S‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_right (JLMS.norm_evaluation_le (𝕜 := 𝕜) y) (norm_nonneg _)).trans
    rw [one_mul]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (JLMS.norm_disjointSynthesis_le η hu hη) (norm_nonneg S)
  have he (n : ℕ) : φ (JLMS.cZeroUnit 𝕜 n) = wolfeBlockImage S (V n) (hV n) y := by
    simp only [φ, A, ContinuousLinearMap.comp_apply, JLMS.disjointSynthesis_unit,
      JLMS.evaluation_apply]
    rfl
  simpa only [he] using h.trans hφ

def wolfeBlockOpen (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (V : Set L) (hV : IsClopen V) (δ : ℝ) : Set K := {y | δ < ‖wolfeBlockImage S V hV y‖}

theorem wolfeBlockOpen_isOpen (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (V : Set L) (hV : IsClopen V) (δ : ℝ) : IsOpen (wolfeBlockOpen S V hV δ) :=
  isOpen_lt continuous_const (wolfeBlockImage S V hV).continuous.norm

theorem wolfeBlockOpen_finite_overlap (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (hd : Pairwise fun n m => Disjoint (V n) (V m))
    (δ : ℝ) (s : Finset ℕ) (y : K)
    (hy : ∀ n ∈ s, y ∈ wolfeBlockOpen S (V n) (hV n) δ) :
    (s.card : ℝ) * δ ≤ ‖S‖ := by
  calc
    (s.card : ℝ) * δ = ∑ n ∈ s, δ := by simp
    _ ≤ ∑ n ∈ s, ‖wolfeBlockImage S (V n) (hV n) y‖ :=
      Finset.sum_le_sum (fun n hn => (hy n hn).le)
    _ ≤ ‖S‖ := wolfeBlockImage_finite_budget S V hV hd s y

section Factorization
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationLift_block_pairing
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (V : Set L) (hV : IsClopen V) (x : L) :
    wolfeFactorizationLift T R c x (wolfeBlockImage S V hV) = if x ∈ V then c else 0 := by
  have he := DFunLike.congr_fun (wolfeFactorizationLift_pullback T R S hfactor c x)
    (wolfeSourceBlock V hV)
  change wolfeFactorizationLift T R c x (S (wolfeSourceBlock V hV)) =
    c * wolfeSourceBlock V hV x at he
  simpa only [wolfeBlockImage, wolfeSourceBlock_apply, mul_ite, mul_one, mul_zero] using he

end Factorization
end Posets
