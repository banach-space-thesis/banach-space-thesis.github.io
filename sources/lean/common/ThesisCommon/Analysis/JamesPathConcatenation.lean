import ThesisCommon.Analysis.JamesSequenceLpEmbedding

/-! Concatenating two separated increasing paths. The cross-gap difference
is retained, so finite-p variation powers dominate the sum of both blocks.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
namespace JamesPath

def append (s t : JamesPath) (h : s.index (Fin.last s.length) < t.index 0) : JamesPath where
  length := s.length + t.length + 1
  index i := if hi : i.val ≤ s.length then s.index ⟨i.val, by omega⟩
    else t.index ⟨i.val - (s.length + 1), by have := i.isLt; omega⟩
  strictMono := by
    intro i j hij
    have hij' : i.val < j.val := hij
    dsimp
    split_ifs with hi hj
    · exact s.strictMono hij'
    · exact (s.strictMono.monotone (Fin.le_last _)).trans_lt
        (h.trans_le (t.strictMono.monotone (Fin.zero_le _)))
    · omega
    · apply t.strictMono
      change i.val - (s.length + 1) < j.val - (s.length + 1)
      omega

def appendLeftEdges (s t : JamesPath) : Fin s.length ↪ Fin (s.length + t.length + 1) where
  toFun j := ⟨j.val, by have := j.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun z : Fin (s.length + t.length + 1) => z.val) h

def appendRightEdges (s t : JamesPath) : Fin t.length ↪ Fin (s.length + t.length + 1) where
  toFun j := ⟨s.length + 1 + j.val, by have := j.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

def appendEdges (s t : JamesPath) : (Fin s.length ⊕ Fin t.length) ↪
    Fin (s.length + t.length + 1) where
  toFun := Sum.elim (s.appendLeftEdges t) (s.appendRightEdges t)
  inj' := by
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl ((s.appendLeftEdges t).injective h)
      | inr j =>
        have := congrArg Fin.val h
        have := i.isLt
        dsimp [appendLeftEdges, appendRightEdges] at *
        omega
    | inr i =>
      cases j with
      | inl j =>
        have := congrArg Fin.val h
        have := j.isLt
        dsimp [appendLeftEdges, appendRightEdges] at *
        omega
      | inr j => exact congrArg Sum.inr ((s.appendRightEdges t).injective h)

end JamesPath
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent)

theorem jamesPath_append_left (s t : JamesPath)
    (h : s.index (Fin.last s.length) < t.index 0) (x : CZeroSum 𝕜) (j : Fin s.length) :
    jamesPathMap 𝕜 p (s.append t h) x (s.appendLeftEdges t j) = jamesPathMap 𝕜 p s x j := by
  have h1 : j.val ≤ s.length := by omega
  have h2 : j.val + 1 ≤ s.length := by omega
  change x ((s.append t h).index ⟨j.val, _⟩) -
    x ((s.append t h).index ⟨j.val + 1, _⟩) = _
  simp only [JamesPath.append, dif_pos h1, dif_pos h2]
  rfl

theorem jamesPath_append_right (s t : JamesPath)
    (h : s.index (Fin.last s.length) < t.index 0) (x : CZeroSum 𝕜) (j : Fin t.length) :
    jamesPathMap 𝕜 p (s.append t h) x (s.appendRightEdges t j) = jamesPathMap 𝕜 p t x j := by
  have h1 : ¬ s.length + 1 + j.val ≤ s.length := by omega
  have h2 : ¬ s.length + 1 + j.val + 1 ≤ s.length := by omega
  change x ((s.append t h).index ⟨s.length + 1 + j.val, _⟩) -
    x ((s.append t h).index ⟨s.length + 1 + j.val + 1, _⟩) = _
  simp only [JamesPath.append, dif_neg h1, dif_neg h2]
  change x (t.index _) - x (t.index _) = x (t.index j.castSucc) - x (t.index j.succ)
  congr 3 <;> apply Fin.ext <;> dsimp <;> omega

theorem jamesPath_append_norm_rpow_le (hp : p.val ≠ ∞) (s t : JamesPath)
    (h : s.index (Fin.last s.length) < t.index 0) (x : CZeroSum 𝕜) :
    ‖jamesPathMap 𝕜 p s x‖ ^ p.val.toReal + ‖jamesPathMap 𝕜 p t x‖ ^ p.val.toReal ≤
      ‖jamesPathMap 𝕜 p (s.append t h) x‖ ^ p.val.toReal := by
  classical
  rw [finitePiLp_norm_rpow p hp, finitePiLp_norm_rpow p hp, finitePiLp_norm_rpow p hp]
  let e := s.appendEdges t
  let v := jamesPathMap 𝕜 p (s.append t h) x
  calc
    _ = ∑ j : Fin s.length ⊕ Fin t.length, ‖v (e j)‖ ^ p.val.toReal := by
      rw [Fintype.sum_sum_type]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun z : 𝕜 => ‖z‖ ^ p.val.toReal)
          (jamesPath_append_left p s t h x j).symm
      · apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun z : 𝕜 => ‖z‖ ^ p.val.toReal)
          (jamesPath_append_right p s t h x j).symm
    _ = ∑ j ∈ Finset.univ.image e, ‖v j‖ ^ p.val.toReal := by
      rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) _)

end ThesisCommon
