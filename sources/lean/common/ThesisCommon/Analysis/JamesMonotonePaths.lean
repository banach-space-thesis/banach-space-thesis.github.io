import ThesisCommon.Analysis.JamesRawPaths

/-! Repeated consecutive nodes contribute no James variation. A finite
nondecreasing path can be compressed to an actual strictly increasing path
without changing its difference energy. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
namespace JamesPath

def point (n : ℕ) : JamesPath where
  length := 0
  index _ := n
  strictMono := by intro i j hij; have := i.isLt; have := j.isLt; omega

def snoc (s : JamesPath) (n : ℕ) (hn : s.index (Fin.last s.length) < n) : JamesPath where
  length := s.length + 1
  index i := if hi : i.val ≤ s.length then s.index ⟨i.val, by omega⟩ else n
  strictMono := by
    intro i j hij
    have hij' : i.val < j.val := hij
    dsimp
    split_ifs with hi hj
    · exact s.strictMono hij'
    · exact (s.strictMono.monotone (Fin.le_last _)).trans_lt hn
    · omega
    · have := i.isLt; have := j.isLt; omega

@[simp] theorem snoc_castSucc (s : JamesPath) (n : ℕ)
    (hn : s.index (Fin.last s.length) < n) (i : Fin (s.length + 1)) :
    (s.snoc n hn).index i.castSucc = s.index i := by
  have hi : i.val ≤ s.length := by omega
  simp only [snoc, Fin.coe_castSucc, dif_pos hi]

@[simp] theorem snoc_last (s : JamesPath) (n : ℕ)
    (hn : s.index (Fin.last s.length) < n) :
    (s.snoc n hn).index (Fin.last (s.length + 1)) = n := by
  simp [snoc]

theorem snoc_energy (s : JamesPath) (n : ℕ)
    (hn : s.index (Fin.last s.length) < n) (w : ℕ → ℕ → ℝ) :
    (∑ j : Fin (s.snoc n hn).length,
      w ((s.snoc n hn).index j.castSucc) ((s.snoc n hn).index j.succ)) =
    (∑ j : Fin s.length, w (s.index j.castSucc) (s.index j.succ)) +
      w (s.index (Fin.last s.length)) n := by
  change (∑ j : Fin (s.length + 1),
    w ((s.snoc n hn).index j.castSucc) ((s.snoc n hn).index j.succ)) = _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.succ_castSucc, snoc_castSucc, Fin.succ_last, snoc_last]

end JamesPath

/-- Compress a finite monotone path, retaining its endpoint and every
nonzero edge contribution. The weight only needs to vanish on the diagonal. -/
theorem exists_jamesPath_of_monotone (w : ℕ → ℕ → ℝ) (hw : ∀ n, w n n = 0)
    {n : ℕ} (f : Fin (n + 1) → ℕ) (hf : Monotone f) :
    ∃ s : JamesPath, s.index (Fin.last s.length) = f (Fin.last n) ∧
      (∑ j : Fin n, w (f j.castSucc) (f j.succ)) =
        ∑ j : Fin s.length, w (s.index j.castSucc) (s.index j.succ) := by
  induction n with
  | zero => exact ⟨JamesPath.point (f 0), rfl, rfl⟩
  | succ n ih =>
    let g : Fin (n + 1) → ℕ := fun i => f i.castSucc
    obtain ⟨s, hs, he⟩ := ih g (hf.comp Fin.strictMono_castSucc.monotone)
    have hle : f (Fin.last n).castSucc ≤ f (Fin.last (n + 1)) :=
      hf (Fin.le_last _)
    have hsum : (∑ j : Fin (n + 1), w (f j.castSucc) (f j.succ)) =
        (∑ j : Fin n, w (g j.castSucc) (g j.succ)) +
          w (g (Fin.last n)) (f (Fin.last (n + 1))) := by
      rw [Fin.sum_univ_castSucc]
      simp only [g, Fin.succ_castSucc, Fin.succ_last]
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hn : s.index (Fin.last s.length) < f (Fin.last (n + 1)) := hs ▸ hlt
      refine ⟨s.snoc (f (Fin.last (n + 1))) hn, JamesPath.snoc_last _ _ _, ?_⟩
      rw [JamesPath.snoc_energy, ← he, hs]
      exact hsum
    · refine ⟨s, hs.trans heq, ?_⟩
      rw [hsum, show g (Fin.last n) = f (Fin.last (n + 1)) from heq, hw, add_zero]
      exact he

variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem james_monotone_path_norm_le {n : ℕ} (f : Fin (n + 1) → ℕ) (hf : Monotone f)
    (x : JamesSequenceSpace 𝕜 p) :
    ‖WithLp.toLp p.val (fun j : Fin n => x (f j.castSucc) - x (f j.succ))‖ ≤ ‖x‖ := by
  have hq : 0 < p.val.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  obtain ⟨s, _, hs⟩ := exists_jamesPath_of_monotone
    (fun i j => ‖x i - x j‖ ^ p.val.toReal)
    (fun i => by dsimp; rw [sub_self, norm_zero, Real.zero_rpow hq.ne']) f hf
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hq).mp
  rw [finitePiLp_norm_rpow p hp]
  change (∑ j : Fin n, ‖x (f j.castSucc) - x (f j.succ)‖ ^ p.val.toReal) ≤ _
  rw [hs]
  change (∑ j, ‖jamesPathMap 𝕜 p s x.val j‖ ^ p.val.toReal) ≤ _
  rw [← finitePiLp_norm_rpow p hp (jamesPathMap 𝕜 p s x.val)]
  exact Real.rpow_le_rpow (norm_nonneg _) (x.path_norm_le s) hq.le

end ThesisCommon
