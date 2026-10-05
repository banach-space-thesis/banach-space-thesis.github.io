import ThesisCommon.Analysis.JamesInitialTruncations
import ThesisCommon.Analysis.FiniteLpZeroExtension

/-! A cut finite path consists of its surviving suffix and one boundary
coordinate. Both pieces are bounded in their actual finite lp norms. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
namespace JamesPath

def suffix (s : JamesPath) (j : Fin (s.length + 1)) : JamesPath where
  length := s.length - j.val
  index i := s.index ⟨j.val + i.val, by have := i.isLt; have := j.isLt; omega⟩
  strictMono := by
    intro a b hab
    apply s.strictMono
    change j.val + a.val < j.val + b.val
    exact Nat.add_lt_add_left hab _

def suffixEdges (s : JamesPath) (j : Fin (s.length + 1)) :
    Fin (s.length - j.val) ↪ Fin s.length where
  toFun r := ⟨j.val + r.val, by have := j.isLt; have := r.isLt; omega⟩
  inj' := by
    intro a b hab
    apply Fin.ext
    have := congrArg (fun r : Fin s.length => r.val) hab
    dsimp at this
    omega

end JamesPath
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}

theorem james_suffix_edge (s : JamesPath) (j : Fin (s.length + 1))
    (x : CZeroSum 𝕜) (r : Fin (s.length - j.val)) :
    jamesPathMap 𝕜 p (s.suffix j) x r =
      jamesPathMap 𝕜 p s x (s.suffixEdges j r) := by
  change x (s.index ⟨j.val + r.val, _⟩) - x (s.index ⟨j.val + (r.val + 1), _⟩) =
    x (s.index ⟨j.val + r.val, _⟩) - x (s.index ⟨j.val + r.val + 1, _⟩)
  simp only [Nat.add_assoc]

theorem james_suffix_extend_apply (s : JamesPath) (j : Fin (s.length + 1))
    (x : CZeroSum 𝕜) (r : Fin s.length) :
    finiteLpExtend p (s.suffixEdges j) (jamesPathMap 𝕜 p (s.suffix j) x) r =
      if j.val ≤ r.val then jamesPathMap 𝕜 p s x r else 0 := by
  by_cases hr : j.val ≤ r.val
  · let i : Fin (s.length - j.val) := ⟨r.val - j.val, by have := r.isLt; omega⟩
    have hi : s.suffixEdges j i = r := by apply Fin.ext; dsimp [JamesPath.suffixEdges, i]; omega
    rw [if_pos hr, ← hi, finiteLpExtend_apply_image]
    exact james_suffix_edge s j x i
  · rw [if_neg hr]
    apply finiteLpExtend_apply_off_range
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    dsimp [JamesPath.suffixEdges] at this
    omega

theorem james_tail_path_norm_le_suffix (x : JamesSequenceSpace 𝕜 p) (N : ℕ)
    (s : JamesPath) (j : Fin (s.length + 1)) (hj : 0 < j.val)
    (hbefore : ∀ i : Fin (s.length + 1), i.val < j.val → s.index i ≤ N)
    (hafter : N < s.index j) :
    ‖jamesPathMap 𝕜 p s (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) N x).val‖ ≤
      ‖jamesPathMap 𝕜 p (s.suffix j) x.val‖ + ‖x (s.index j)‖ := by
  classical
  let c : Fin s.length := ⟨j.val - 1, by have := j.isLt; omega⟩
  let z : PiLp p.val (fun _ : Fin s.length => 𝕜) :=
    WithLp.toLp p.val (Pi.single c (-x (s.index j)))
  let w := finiteLpExtend p (s.suffixEdges j) (jamesPathMap 𝕜 p (s.suffix j) x.val)
  have heq : jamesPathMap 𝕜 p s (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) N x).val = w + z := by
    ext r
    change (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) N x) (s.index r.castSucc) -
      (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) N x) (s.index r.succ) = w r + z r
    rw [JamesSequenceSpace.tail_apply, JamesSequenceSpace.tail_apply]
    change _ = finiteLpExtend p (s.suffixEdges j)
      (jamesPathMap 𝕜 p (s.suffix j) x.val) r +
        (Pi.single c (-x (s.index j)) : Fin s.length → 𝕜) r
    rw [james_suffix_extend_apply]
    by_cases hr : j.val ≤ r.val
    · have hleft : N < s.index r.castSucc :=
        hafter.trans_le (s.strictMono.monotone (by exact hr))
      have hright : N < s.index r.succ := hleft.trans (s.strictMono (Fin.castSucc_lt_succ r))
      have hrc : r ≠ c := by
        intro he
        have := congrArg Fin.val he
        dsimp [c] at this
        omega
      simp [hr, hleft.not_ge, hright.not_ge, hrc,
        jamesPathMap_apply]
    · have hleft : s.index r.castSucc ≤ N := hbefore r.castSucc (by exact Nat.lt_of_not_ge hr)
      by_cases hlt : r.val + 1 < j.val
      · have hright : s.index r.succ ≤ N := hbefore r.succ hlt
        have hrc : r ≠ c := by
          intro he
          have := congrArg Fin.val he
          dsimp [c] at this
          omega
        simp [hr, hleft, hright, hrc]
      · have he : r.succ = j := by apply Fin.ext; dsimp; omega
        have hrc : r = c := by apply Fin.ext; dsimp [c]; omega
        rw [he]
        rw [if_pos hleft, if_neg hafter.not_ge, if_neg hr, zero_sub, zero_add]
        rw [← hrc, Pi.single_eq_same]
  rw [heq]
  apply (norm_add_le w z).trans
  apply add_le_add (finiteLpExtend_norm_le p _ _)
  change ‖WithLp.toLp p.val (Pi.single c (-x (s.index j)) : Fin s.length → 𝕜)‖ ≤
    ‖x (s.index j)‖
  simp only [PiLp.norm_toLp_single, norm_neg, le_refl]

end ThesisCommon

