import JLMS.Bonsall

/-!
# Section 8: the Eidelheit–Yood minimality contradiction

The simultaneous factorization construction of Lemma 8.2 is an explicit input.
The contradiction below follows the paper: failure of a lower norm comparison
produces operators with arbitrarily large essential norm and arbitrarily small
competing norm. Simultaneous compression by fixed U,V is then impossible.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Failure of minimality allows simultaneous control of the two norms by scaling. -/
theorem small_calkinNorm_of_not_minimal
    (n : Calkin 𝕜 E → ℝ) (hn : IsCalkinAlgebraNorm 𝕜 E n)
    (hnot : ¬ ∃ c : ℝ, 0 < c ∧
      ∀ T : E →L[𝕜] E, c * essentialNorm T ≤ n (calkinMk 𝕜 E T))
    (M η : ℝ) (hM : 0 < M) (hη : 0 < η) :
    ∃ T : E →L[𝕜] E, M < essentialNorm T ∧ n (calkinMk 𝕜 E T) < η := by
  have hc : 0 < η / (M + 1) := div_pos hη (by linarith)
  have hfailure : ¬ ∀ T : E →L[𝕜] E,
      (η / (M + 1)) * essentialNorm T ≤ n (calkinMk 𝕜 E T) :=
    fun h => hnot ⟨η / (M + 1), hc, h⟩
  push_neg at hfailure
  obtain ⟨R, hR⟩ := hfailure
  have he : 0 < essentialNorm R := by
    have hnR := hn.1.1 (calkinMk 𝕜 E R)
    by_contra he
    have : η / (M + 1) * essentialNorm R ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt he)
    linarith
  let a : 𝕜 := ((M + 1) / essentialNorm R : ℝ)
  have ha : ‖a‖ = (M + 1) / essentialNorm R := by
    change ‖(((M + 1) / essentialNorm R : ℝ) : 𝕜)‖ = _
    rw [RCLike.norm_ofReal, abs_of_pos (div_pos (by linarith) he)]
  refine ⟨a • R, ?_, ?_⟩
  · rw [essentialNorm_smul, ha, div_mul_cancel₀ _ (ne_of_gt he)]
    linarith
  · have hclass : calkinMk 𝕜 E (a • R) = a • calkinMk 𝕜 E R :=
      Submodule.Quotient.mk_smul _ _ _
    rw [hclass, hn.1.2.2.2, ha]
    have hapos : 0 < (M + 1) / essentialNorm R := div_pos (by linarith) he
    have hscale := mul_lt_mul_of_pos_left hR hapos
    have hcancel : ((M + 1) / essentialNorm R) *
        (η / (M + 1) * essentialNorm R) = η := by
      field_simp
    rw [hcancel] at hscale
    exact hscale

/-- The operator-theoretic input supplied by Lemma 8.2. Defining this
proposition does not assert that any space has simultaneous factorizations. -/
def SimultaneousFactorizations (P : ℕ → E →L[𝕜] E) (M : ℕ → ℝ) : Prop :=
  ∀ T : ℕ → E →L[𝕜] E, (∀ j, M j < essentialNorm (T j)) →
    ∃ U V : E →L[𝕜] E, ∀ j,
      (((P j).comp U).comp (T j)).comp (V.comp (P j)) = P j

/-- The minimality part of Theorem 1.1, conditional only on the simultaneous
factorization input and the noncompact idempotent family used there. -/
theorem essentialNormIsMinimal_of_simultaneous
    (P : ℕ → E →L[𝕜] E) (M : ℕ → ℝ) (hM : ∀ j, 0 < M j)
    (hidem : ∀ j, (P j).comp (P j) = P j)
    (hcompact : ∀ j, ¬ IsCompactOperator (P j))
    (hfactor : SimultaneousFactorizations P M) : EssentialNormIsMinimal 𝕜 E := by
  intro n hn
  by_contra hnot
  let q : ℕ → ℝ := fun j => n (calkinMk 𝕜 E (P j))
  have hq (j : ℕ) : 1 ≤ q j := one_le_calkinNorm_of_idempotent n hn (P j) (hidem j) (hcompact j)
  have hqpos (j : ℕ) : 0 < q j := lt_of_lt_of_le zero_lt_one (hq j)
  have hden (j : ℕ) : 0 < ((j : ℝ) + 1) * (q j) ^ 2 := by
    have hqj := hqpos j
    positivity
  choose T hlarge hsmall using fun j => small_calkinNorm_of_not_minimal n hn hnot (M j)
    (1 / (((j : ℝ) + 1) * (q j) ^ 2)) (hM j) (one_div_pos.mpr (hden j))
  obtain ⟨U, V, hcompression⟩ := hfactor T hlarge
  let u := n (calkinMk 𝕜 E U)
  let v := n (calkinMk 𝕜 E V)
  have hu : 0 ≤ u := hn.1.1 _
  have hv : 0 ≤ v := hn.1.1 _
  obtain ⟨j, hj⟩ := exists_nat_gt (u * v)
  have hqj := hqpos j
  have hsub₁ := hn.2 (((P j).comp U).comp (T j)) (V.comp (P j))
  have hsub₂ := hn.2 ((P j).comp U) (T j)
  have hsub₃ := hn.2 (P j) U
  have hsub₄ := hn.2 V (P j)
  rw [hcompression j] at hsub₁
  have ht : 0 ≤ n (calkinMk 𝕜 E (T j)) := hn.1.1 _
  have hright : 0 ≤ n (calkinMk 𝕜 E (V.comp (P j))) := hn.1.1 _
  have hleft : n (calkinMk 𝕜 E (((P j).comp U).comp (T j))) ≤
      (q j * u) * n (calkinMk 𝕜 E (T j)) :=
    hsub₂.trans (mul_le_mul_of_nonneg_right hsub₃ ht)
  have hbound : q j ≤ (q j) ^ 2 * (u * v) * n (calkinMk 𝕜 E (T j)) := by
    calc
      q j ≤ n (calkinMk 𝕜 E (((P j).comp U).comp (T j))) *
          n (calkinMk 𝕜 E (V.comp (P j))) := hsub₁
      _ ≤ ((q j * u) * n (calkinMk 𝕜 E (T j))) * (v * q j) :=
        mul_le_mul hleft hsub₄ hright (by positivity)
      _ = (q j) ^ 2 * (u * v) * n (calkinMk 𝕜 E (T j)) := by ring
  have hscaled := mul_le_mul_of_nonneg_left (hsmall j).le
    (show 0 ≤ (q j) ^ 2 * (u * v) by positivity)
  have hcancel : (q j) ^ 2 * (u * v) * (1 / (((j : ℝ) + 1) * (q j) ^ 2)) =
      (u * v) / ((j : ℝ) + 1) := by
    field_simp [ne_of_gt hqj]
  rw [hcancel] at hscaled
  have hone : 1 ≤ (u * v) / ((j : ℝ) + 1) := (hq j).trans (hbound.trans hscaled)
  have hlast := (le_div_iff₀ (show 0 < (j : ℝ) + 1 by positivity)).mp hone
  linarith

end JLMS
