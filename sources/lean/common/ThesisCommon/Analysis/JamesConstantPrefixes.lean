import ThesisCommon.Analysis.JamesRawPaths

/-! The initial sections of the constant-one sequence have James norm one.
The bound retains the single crossing edge of every increasing path. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesConstantPrefix (N : ℕ) : JamesSequenceSpace 𝕜 p :=
  jamesFiniteSequence p hp (fun _ => (1 : 𝕜)) N

@[simp] theorem jamesConstantPrefix_apply (N n : ℕ) :
    jamesConstantPrefix (𝕜 := 𝕜) p hp N n = if n ≤ N then 1 else 0 :=
  jamesFiniteSequence_apply p hp _ N n

theorem jamesConstantPrefix_norm_le (N : ℕ) :
    ‖jamesConstantPrefix (𝕜 := 𝕜) p hp N‖ ≤ 1 := by
  classical
  have hq : 0 < p.val.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  apply JamesSequenceSpace.norm_le
  intro s
  have hv (j : Fin s.length) :
      jamesPathMap 𝕜 p s (jamesConstantPrefix (𝕜 := 𝕜) p hp N).val j =
        if s.index j.castSucc ≤ N ∧ N < s.index j.succ then 1 else 0 := by
    simp only [jamesPathMap_apply, jamesConstantPrefix_apply]
    have hs := s.strictMono (Fin.castSucc_lt_succ j)
    split_ifs <;> simp_all <;> omega
  let S := Finset.univ.filter (fun j : Fin s.length =>
    s.index j.castSucc ≤ N ∧ N < s.index j.succ)
  have hcard : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨_, hil, hir⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, hjl, hjr⟩ := Finset.mem_filter.mp hj
    apply le_antisymm
    · by_contra hn
      have hij : j.succ ≤ i.castSucc := by change j.val + 1 ≤ i.val; exact Nat.lt_of_not_ge hn
      have hh := s.strictMono.monotone hij
      omega
    · by_contra hn
      have hij : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; exact Nat.lt_of_not_ge hn
      have hh := s.strictMono.monotone hij
      omega
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) zero_le_one hq).mp
  rw [finitePiLp_norm_rpow p hp, Real.one_rpow]
  have hsum : (∑ j : Fin s.length,
      ‖jamesPathMap 𝕜 p s (jamesConstantPrefix (𝕜 := 𝕜) p hp N).val j‖ ^ p.val.toReal) =
        (S.card : ℝ) := by
    have hv' (j : Fin s.length) :
        ‖jamesPathMap 𝕜 p s (jamesConstantPrefix (𝕜 := 𝕜) p hp N).val j‖ ^ p.val.toReal =
          if s.index j.castSucc ≤ N ∧ N < s.index j.succ then (1 : ℝ) else 0 := by
      rw [hv]
      split_ifs <;> simp [Real.zero_rpow hq.ne']
    simp only [hv']
    simp [S]
  rw [hsum]
  exact_mod_cast hcard

theorem jamesConstantPrefix_initial (K N : ℕ) (hKN : K ≤ N) :
    JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) K (jamesConstantPrefix p hp N) =
      jamesConstantPrefix p hp K := by
  ext n
  by_cases hn : n ≤ K
  · simp [JamesSequenceSpace.initial_apply, hn, hn.trans hKN]
  · simp [JamesSequenceSpace.initial_apply, hn]

end ThesisCommon
