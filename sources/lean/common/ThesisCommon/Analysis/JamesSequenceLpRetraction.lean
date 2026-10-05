import ThesisCommon.Analysis.JamesSequenceLpEmbedding
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Abel

/-! The actual bounded retraction from James space to lp obtained by adjacent
even/odd differences. Initial James paths dominate every partial sum of its
pth powers, proving genuine lp membership and the contraction estimate.
Together with even-coordinate insertion this gives a complemented lp copy.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesInitialPath (N : ℕ) : JamesPath where
  length := N
  index := Fin.val
  strictMono := fun _ _ h => h

def jamesEvenFiniteEmbedding (N : ℕ) : Fin N ↪ Fin (2 * N) where
  toFun j := ⟨2 * j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' := congrArg Fin.val h
    dsimp at h'
    omega

include hp in
theorem jamesLpRead_sum_range_le (x : JamesSequenceSpace 𝕜 p) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖x (2 * n) - x (2 * n + 1)‖ ^ p.val.toReal ≤
      ‖x‖ ^ p.val.toReal := by
  classical
  let v := jamesPathMap 𝕜 p (jamesInitialPath (2 * N)) x.val
  let e := jamesEvenFiniteEmbedding N
  have hs : (∑ j : Fin N, ‖v (e j)‖ ^ p.val.toReal) ≤
      ∑ j : Fin (2 * N), ‖v j‖ ^ p.val.toReal := by
    calc
      _ = ∑ j ∈ Finset.univ.image e, ‖v j‖ ^ p.val.toReal :=
        (Finset.sum_image (fun _ _ _ _ h => e.injective h)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hfin : (∑ j : Fin N, ‖x (2 * j.val) - x (2 * j.val + 1)‖ ^ p.val.toReal) ≤
      ‖x‖ ^ p.val.toReal := by
    calc
      _ = ∑ j : Fin N, ‖v (e j)‖ ^ p.val.toReal := rfl
      _ ≤ ∑ j : Fin (2 * N), ‖v j‖ ^ p.val.toReal := hs
      _ = ‖v‖ ^ p.val.toReal := (finitePiLp_norm_rpow p hp v).symm
      _ ≤ ‖x‖ ^ p.val.toReal := Real.rpow_le_rpow (norm_nonneg _)
        (JamesSequenceSpace.path_norm_le x _) ENNReal.toReal_nonneg
  rwa [Fin.sum_univ_eq_sum_range
    (fun n => ‖x (2 * n) - x (2 * n + 1)‖ ^ p.val.toReal)] at hfin

def jamesLpReadValue (x : JamesSequenceSpace 𝕜 p) : SequenceSum p 𝕜 :=
  ⟨fun n => x (2 * n) - x (2 * n + 1),
    memℓp_gen (summable_of_sum_range_le
      (fun _ => Real.rpow_nonneg (norm_nonneg _) _) (jamesLpRead_sum_range_le p hp x))⟩

theorem norm_jamesLpReadValue_le (x : JamesSequenceSpace 𝕜 p) :
    ‖jamesLpReadValue p hp x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp) (norm_nonneg x)
  exact Real.tsum_le_of_sum_range_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (jamesLpRead_sum_range_le p hp x)

/-- Read adjacent even/odd differences. This is an actual contraction into lp. -/
def jamesLpRead : JamesSequenceSpace 𝕜 p →L[𝕜] SequenceSum p 𝕜 :=
  LinearMap.mkContinuous
    { toFun := jamesLpReadValue p hp
      map_add' := by
        intro x y
        ext n
        change (x (2 * n) + y (2 * n)) - (x (2 * n + 1) + y (2 * n + 1)) =
          (x (2 * n) - x (2 * n + 1)) + (y (2 * n) - y (2 * n + 1))
        abel
      map_smul' := by
        intro c x
        ext n
        exact (smul_sub c (x (2 * n)) (x (2 * n + 1))).symm }
    1 (fun x => by simpa only [one_mul] using norm_jamesLpReadValue_le p hp x)

@[simp] theorem jamesLpRead_apply (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    jamesLpRead (𝕜 := 𝕜) p hp x n = x (2 * n) - x (2 * n + 1) := rfl

theorem norm_jamesLpRead_le : ‖jamesLpRead (𝕜 := 𝕜) p hp‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The recovery identity for the concrete lp copy. -/
theorem jamesLpRead_comp_insert :
    (jamesLpRead (𝕜 := 𝕜) p hp).comp (jamesLpInsert p hp) =
      ContinuousLinearMap.id 𝕜 (SequenceSum p 𝕜) := by
  ext a n
  change jamesLpInsert (𝕜 := 𝕜) p hp a (2 * n) -
    jamesLpInsert (𝕜 := 𝕜) p hp a (2 * n + 1) = a n
  rw [jamesLpInsert_even, jamesLpInsert_odd, sub_zero]

/-- The actual bounded projection onto the inserted copy. -/
def jamesLpProjection : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  (jamesLpInsert p hp).comp (jamesLpRead p hp)

theorem jamesLpProjection_idempotent :
    (jamesLpProjection (𝕜 := 𝕜) p hp).comp (jamesLpProjection p hp) =
      jamesLpProjection p hp := by
  apply ContinuousLinearMap.ext
  intro x
  change jamesLpInsert (𝕜 := 𝕜) p hp (jamesLpRead (𝕜 := 𝕜) p hp
    (jamesLpInsert (𝕜 := 𝕜) p hp (jamesLpRead (𝕜 := 𝕜) p hp x))) =
      jamesLpInsert (𝕜 := 𝕜) p hp (jamesLpRead (𝕜 := 𝕜) p hp x)
  have h := congrArg (fun T : SequenceSum p 𝕜 →L[𝕜] SequenceSum p 𝕜 =>
    T (jamesLpRead (𝕜 := 𝕜) p hp x)) (jamesLpRead_comp_insert (𝕜 := 𝕜) p hp)
  exact congrArg (jamesLpInsert (𝕜 := 𝕜) p hp) h

theorem norm_jamesLpProjection_le : ‖jamesLpProjection (𝕜 := 𝕜) p hp‖ ≤ 2 := by
  apply le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
  have h := mul_le_mul (norm_jamesLpInsert_le (𝕜 := 𝕜) p hp)
    (norm_jamesLpRead_le (𝕜 := 𝕜) p hp) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_one] using h

end ThesisCommon
