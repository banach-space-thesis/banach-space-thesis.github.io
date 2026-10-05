import ThesisCommon.Analysis.JamesMonotonePathEndpoints
import ThesisCommon.Analysis.JamesPathConcatenation

/-! Adjacent variation paths may share their common endpoint. Compressing
the resulting nondecreasing path retains both energies, including at a
shared zero boundary between finite James blocks. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon

def jamesJoinedIndex (s t : JamesPath) : Fin (s.length + t.length + 2) → ℕ :=
  fun i => if hi : i.val ≤ s.length then s.index ⟨i.val, by omega⟩
    else t.index ⟨i.val - (s.length + 1), by have := i.isLt; omega⟩

theorem jamesJoinedIndex_monotone (s t : JamesPath)
    (h : s.index (Fin.last s.length) ≤ t.index 0) : Monotone (jamesJoinedIndex s t) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  dsimp [jamesJoinedIndex]
  split_ifs with hi hj
  · exact s.strictMono.monotone hij'
  · exact (s.strictMono.monotone (Fin.le_last _)).trans
      (h.trans (t.strictMono.monotone (Fin.zero_le _)))
  · omega
  · apply t.strictMono.monotone
    change i.val - (s.length + 1) ≤ j.val - (s.length + 1)
    omega

@[simp] theorem jamesJoinedIndex_last (s t : JamesPath) :
    jamesJoinedIndex s t (Fin.last (s.length + t.length + 1)) = t.index (Fin.last t.length) := by
  dsimp [jamesJoinedIndex]
  rw [dif_neg (by omega)]
  congr 1
  apply Fin.ext
  dsimp
  omega

theorem jamesJoinedIndex_left (s t : JamesPath) (j : Fin s.length) :
    jamesJoinedIndex s t (s.appendLeftEdges t j).castSucc = s.index j.castSucc ∧
      jamesJoinedIndex s t (s.appendLeftEdges t j).succ = s.index j.succ := by
  have h1 : j.val ≤ s.length := by omega
  have h2 : j.val + 1 ≤ s.length := by omega
  constructor
  · change jamesJoinedIndex s t ⟨j.val, _⟩ = s.index j.castSucc
    simp only [jamesJoinedIndex, dif_pos h1]
    rfl
  · change jamesJoinedIndex s t ⟨j.val + 1, _⟩ = s.index j.succ
    simp only [jamesJoinedIndex, dif_pos h2]
    rfl

theorem jamesJoinedIndex_right (s t : JamesPath) (j : Fin t.length) :
    jamesJoinedIndex s t (s.appendRightEdges t j).castSucc = t.index j.castSucc ∧
      jamesJoinedIndex s t (s.appendRightEdges t j).succ = t.index j.succ := by
  have h1 : ¬ s.length + 1 + j.val ≤ s.length := by omega
  have h2 : ¬ s.length + 1 + j.val + 1 ≤ s.length := by omega
  constructor
  · change jamesJoinedIndex s t ⟨s.length + 1 + j.val, _⟩ = t.index j.castSucc
    simp only [jamesJoinedIndex, dif_neg h1]
    congr 1
    apply Fin.ext
    dsimp
    omega
  · change jamesJoinedIndex s t ⟨s.length + 1 + j.val + 1, _⟩ = t.index j.succ
    simp only [jamesJoinedIndex, dif_neg h2]
    congr 1
    apply Fin.ext
    dsimp
    omega

variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem jamesPath_join_energy (s t : JamesPath)
    (h : s.index (Fin.last s.length) ≤ t.index 0) (a : ℕ → 𝕜) :
    ∃ u : JamesPath, u.index (Fin.last u.length) = t.index (Fin.last t.length) ∧
      ‖jamesRawPath p s a‖ ^ p.val.toReal + ‖jamesRawPath p t a‖ ^ p.val.toReal ≤
        ‖jamesRawPath p u a‖ ^ p.val.toReal := by
  classical
  have hq : 0 < p.val.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  let w : ℕ → ℕ → ℝ := fun i j => ‖a i - a j‖ ^ p.val.toReal
  obtain ⟨u, _, hu, he⟩ := exists_jamesPath_of_monotone_endpoints w
    (fun i => by simp only [w, sub_self, norm_zero, Real.zero_rpow hq.ne'])
    (jamesJoinedIndex s t) (jamesJoinedIndex_monotone s t h)
  refine ⟨u, hu.trans (jamesJoinedIndex_last s t), ?_⟩
  rw [finitePiLp_norm_rpow p hp, finitePiLp_norm_rpow p hp, finitePiLp_norm_rpow p hp]
  change (∑ j : Fin s.length, w (s.index j.castSucc) (s.index j.succ)) +
    (∑ j : Fin t.length, w (t.index j.castSucc) (t.index j.succ)) ≤
    ∑ j : Fin u.length, w (u.index j.castSucc) (u.index j.succ)
  rw [← he]
  let e := s.appendEdges t
  let v := fun j : Fin (s.length + t.length + 1) =>
    w (jamesJoinedIndex s t j.castSucc) (jamesJoinedIndex s t j.succ)
  calc
    _ = ∑ j : Fin s.length ⊕ Fin t.length, v (e j) := by
      rw [Fintype.sum_sum_type]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        exact congrArg₂ w (jamesJoinedIndex_left s t j).1.symm
          (jamesJoinedIndex_left s t j).2.symm
      · apply Finset.sum_congr rfl
        intro j _
        exact congrArg₂ w (jamesJoinedIndex_right s t j).1.symm
          (jamesJoinedIndex_right s t j).2.symm
    _ = ∑ j ∈ Finset.univ.image e, v j := by
      rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) _)

end ThesisCommon
