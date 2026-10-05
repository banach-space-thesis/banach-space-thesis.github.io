import ThesisCommon.Analysis.MixedInfinityEstimates
import ThesisCommon.Analysis.SchauderSumCompression
import ThesisCommon.Analysis.SequenceEntryAlgebra

/-! Canonical coordinate retractions on the actual mixed space X(ell_infinity).
No Schauder basis in ell_infinity is asserted or used. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

def infinityPairEmbedding (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun p := (n p.1, m p.1 p.2)
  inj' := by
    rintro ⟨i, j⟩ ⟨r, s⟩ h
    have hir : i = r := n.injective (congrArg Prod.fst h)
    subst r
    have hjs : j = s := (m i).injective (congrArg Prod.snd h)
    subst s
    rfl

def infinityRestrict (hs : b.HasSymmetricNorm) (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) :
    SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) :=
  (diagonal (b := b) (hb := hb) (fun i => lpRestrict (𝕜 := 𝕜) (X := 𝕜) ∞ (m i)) 1 zero_le_one
    (fun i => norm_lpRestrict_le (m i))).comp (restrictL hs n)

def infinityExtend (hs : b.HasSymmetricNorm) (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) :
    SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) :=
  (extendL (hb := hb) (Y := lp (fun _ : ℕ => 𝕜) ∞) hs n).comp
    (diagonal (fun i => lpExtend (𝕜 := 𝕜) (X := 𝕜) ∞ (m i)) 1 zero_le_one
    (fun i => norm_lpExtend_le (m i)))

@[simp] theorem infinityRestrict_apply (hs : b.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ)
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j : ℕ) :
    infinityRestrict hs n m x i j = x (n i) (m i j) := rfl

theorem infinityExtend_apply_image (hs : b.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ)
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j : ℕ) :
    infinityExtend hs n m x (n i) (m i j) = x i j := by
  change extendL (hb := hb) (Y := lp (fun _ : ℕ => 𝕜) ∞) hs n
    (diagonal (fun i => lpExtend (𝕜 := 𝕜) (X := 𝕜) ∞ (m i)) 1 zero_le_one
    (fun i => norm_lpExtend_le (m i)) x) (n i) (m i j) = _
  rw [extendL_apply, extend_apply, if_pos (Set.mem_range_self i),
    Function.leftInverse_invFun n.injective i, diagonal_apply, lpExtend_apply_image]

theorem infinityExtend_apply_off_range (hs : b.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ)
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) {p : ℕ × ℕ}
    (hp : p ∉ Set.range (infinityPairEmbedding n m)) :
    infinityExtend hs n m x p.1 p.2 = 0 := by
  classical
  change extendL (hb := hb) (Y := lp (fun _ : ℕ => 𝕜) ∞) hs n
    (diagonal (fun i => lpExtend (𝕜 := 𝕜) (X := 𝕜) ∞ (m i)) 1 zero_le_one
    (fun i => norm_lpExtend_le (m i)) x) p.1 p.2 = _
  rw [extendL_apply, extend_apply]
  by_cases hi : p.1 ∈ Set.range n
  · obtain ⟨i, hi⟩ := hi
    rw [← hi, if_pos (Set.mem_range_self i), Function.leftInverse_invFun n.injective i,
      diagonal_apply]
    apply lpExtend_apply_off_range
    rintro ⟨j, hj⟩
    apply hp
    exact ⟨(i, j), Prod.ext hi hj⟩
  · rw [if_neg hi]
    rfl

theorem infinityRestrict_comp_extend (hs : b.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) :
    (infinityRestrict (hb := hb) hs n m).comp (infinityExtend hs n m) =
      ContinuousLinearMap.id 𝕜 _ := by
  ext x i j
  exact infinityExtend_apply_image hs n m x i j

theorem norm_infinityRestrict_le (hs : b.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) :
    ‖infinityRestrict (hb := hb) hs n m‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 1 * 1 := mul_le_mul (norm_diagonal_le _ _ _ _) (norm_restrictL_le hs n)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem norm_infinityExtend_le (hs : b.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) :
    ‖infinityExtend (hb := hb) hs n m‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 1 * 1 := mul_le_mul (norm_extendL_le hs n) (norm_diagonal_le _ _ _ _)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem infinityExtend_single (hs : b.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ) (i j : ℕ) (a : 𝕜) :
    infinityExtend (hb := hb) hs n m (single i (lp.single ∞ j a)) =
      single (n i) (lp.single ∞ (m i j) a) := by
  change extendL (hb := hb) (Y := lp (fun _ : ℕ => 𝕜) ∞) hs n
    (diagonal (fun i => lpExtend (𝕜 := 𝕜) (X := 𝕜) ∞ (m i)) 1 zero_le_one
    (fun i => norm_lpExtend_le (m i)) (single i (lp.single ∞ j a))) = _
  rw [diagonal_single, lpExtend_single, extendL_single]

theorem infinityEntry_compression (hs : b.HasSymmetricNorm)
    (n : ℕ ↪ ℕ) (m : ℕ → ℕ ↪ ℕ)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j r s : ℕ) :
    infinityEntry (((infinityRestrict hs n m).comp T).comp (infinityExtend hs n m)) i j r s =
      infinityEntry T (n i) (m i j) (n r) (m r s) := by
  change T (infinityExtend hs n m (single r (lp.single ∞ s (1 : 𝕜)))) (n i) (m i j) = _
  rw [infinityExtend_single]
  rfl

end SchauderSum
end ThesisCommon
