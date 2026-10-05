import ThesisCommon.Analysis.JamesSchauderBasis

/-! Finite James variation for arbitrary scalar sequences, and its relation
to the actual finitely supported James vectors. These definitions permit
bidual coordinate sequences that need not tend to zero. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesFiniteSequence (a : ℕ → 𝕜) (N : ℕ) : JamesSequenceSpace 𝕜 p :=
  ∑ n ∈ Finset.range (N + 1), a n • jamesUnit p hp n

@[simp] theorem jamesFiniteSequence_apply (a : ℕ → 𝕜) (N n : ℕ) :
    jamesFiniteSequence p hp a N n = if n ≤ N then a n else 0 := by
  simpa only [Finset.mem_range, Nat.lt_succ_iff] using
    james_finite_units_apply p hp (Finset.range (N + 1)) a n

def jamesRawPath (s : JamesPath) (a : ℕ → 𝕜) : PiLp p.val (fun _ : Fin s.length => 𝕜) :=
  WithLp.toLp p.val (fun j => a (s.index j.castSucc) - a (s.index j.succ))

@[simp] theorem jamesRawPath_apply (s : JamesPath) (a : ℕ → 𝕜) (j : Fin s.length) :
    jamesRawPath p s a j = a (s.index j.castSucc) - a (s.index j.succ) := rfl

theorem jamesRawPath_eq_finite (s : JamesPath) (a : ℕ → 𝕜) (N : ℕ)
    (hN : s.index (Fin.last s.length) ≤ N) :
    jamesRawPath p s a = jamesPathMap 𝕜 p s (jamesFiniteSequence p hp a N).val := by
  ext j
  have hl : s.index j.castSucc ≤ N := (s.strictMono.monotone (Fin.le_last _)).trans hN
  have hr : s.index j.succ ≤ N := (s.strictMono.monotone (Fin.le_last _)).trans hN
  simp only [jamesRawPath_apply, jamesPathMap_apply, jamesFiniteSequence_apply,
    if_pos hl, if_pos hr]

include hp in
theorem jamesRawPath_append_rpow_le (s t : JamesPath)
    (h : s.index (Fin.last s.length) < t.index 0) (a : ℕ → 𝕜) :
    ‖jamesRawPath p s a‖ ^ p.val.toReal + ‖jamesRawPath p t a‖ ^ p.val.toReal ≤
      ‖jamesRawPath p (s.append t h) a‖ ^ p.val.toReal := by
  let N := max (s.index (Fin.last s.length))
    (max (t.index (Fin.last t.length))
      ((s.append t h).index (Fin.last (s.append t h).length)))
  rw [jamesRawPath_eq_finite p hp s a N (le_max_left _ _),
    jamesRawPath_eq_finite p hp t a N ((le_max_left _ _).trans (le_max_right _ _)),
    jamesRawPath_eq_finite p hp (s.append t h) a N
      ((le_max_right _ _).trans (le_max_right _ _))]
  exact jamesPath_append_norm_rpow_le p hp s t h _

include hp in
theorem jamesRawPath_far_small (a : ℕ → 𝕜) {C : ℝ}
    (hbound : ∀ s : JamesPath, ‖jamesRawPath p s a‖ ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : JamesPath, N < s.index 0 → ‖jamesRawPath p s a‖ < ε := by
  classical
  have hC : 0 ≤ C := (norm_nonneg (jamesRawPath p (JamesPath.two 0 1 (by omega)) a)).trans
    (hbound _)
  by_contra hn
  push_neg at hn
  have hpower : 0 < ε ^ p.val.toReal := Real.rpow_pos_of_pos hε _
  have hgrow (n : ℕ) : ∃ s : JamesPath,
      (n : ℝ) * ε ^ p.val.toReal ≤ ‖jamesRawPath p s a‖ ^ p.val.toReal := by
    induction n with
    | zero =>
      refine ⟨JamesPath.two 0 1 (by omega), ?_⟩
      simp only [Nat.cast_zero, zero_mul]
      exact Real.rpow_nonneg (norm_nonneg _) _
    | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨t, ht, hnorm⟩ := hn (s.index (Fin.last s.length))
      refine ⟨s.append t ht, ?_⟩
      calc
        ((n + 1 : ℕ) : ℝ) * ε ^ p.val.toReal =
            (n : ℝ) * ε ^ p.val.toReal + ε ^ p.val.toReal := by push_cast; ring
        _ ≤ ‖jamesRawPath p s a‖ ^ p.val.toReal + ‖jamesRawPath p t a‖ ^ p.val.toReal :=
          add_le_add hs (Real.rpow_le_rpow hε.le hnorm ENNReal.toReal_nonneg)
        _ ≤ _ := jamesRawPath_append_rpow_le p hp s t ht a
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ p.val.toReal / ε ^ p.val.toReal)
  have hn' : C ^ p.val.toReal < (n : ℝ) * ε ^ p.val.toReal :=
    (div_lt_iff₀ hpower).mp hn
  obtain ⟨s, hs⟩ := hgrow n
  have hs' : ‖jamesRawPath p s a‖ ^ p.val.toReal ≤ C ^ p.val.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) (hbound s) ENNReal.toReal_nonneg
  exact (not_lt_of_ge (hs.trans hs')) hn'

end ThesisCommon
