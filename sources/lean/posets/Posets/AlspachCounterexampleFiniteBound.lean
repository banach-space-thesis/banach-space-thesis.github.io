import Posets.AlspachCounterexampleSuccessorBound
import Posets.AlspachCounterexampleRankArithmetic

/-! Uniform finite-stage Wolfe bounds at each positive threshold. Doubling
the threshold decreases its depth parameter; the stage parameter contributes
only a finite ordinal remainder, which disappears at the next ω block. -/

noncomputable section
open Set Topology Order ThesisCommon
open scoped Ordinal
namespace Posets
namespace AlspachCompactRows
variable {𝕜 : Type*} [RCLike 𝕜] (F : AlspachCompactRows 𝕜)

theorem wolfe_empty_of_one_lt {ε : ℝ} (hε : 1 < ε) (α : Ordinal) :
    wolfeFamily F.pointAtomicModel ε (range F.weakRows) α = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨μ, U⟩ h
  obtain ⟨⟨i, rfl⟩, _, hm⟩ := wolfeFamily_subset_base F.pointAtomicModel ε _ α h
  rw [F.weakRows_mass] at hm
  exact hε.not_ge (hm.trans ((F.rows.row i).mass_le_one U))

theorem wolfe_empty_mono {ε : ℝ} {α β : Ordinal}
    (hβ : β.card ≤ Cardinal.aleph0) (hαβ : α ≤ β)
    (h : wolfeFamily F.pointAtomicModel ε (range F.weakRows) α = ∅) :
    wolfeFamily F.pointAtomicModel ε (range F.weakRows) β = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := wolfeFamily_antitone_on_countable F.pointAtomicModel ε _ hβ hαβ hz
  rw [h] at hh
  exact hh

theorem wolfe_empty_of_index_rank {ε : ℝ} (hε : 0 < ε) (α : Ordinal)
    (h : ordinalDerived (univ : Set F.Index) α = ∅) :
    wolfeFamily F.pointAtomicModel ε (range F.weakRows) α = ∅ := by
  apply wolfeFamily_empty_of_ordinalDerived_empty F.pointAtomicModel hε F.weakRows_range_closed
  rw [← image_univ, ordinalDerived_image_closedEmbedding F.weakRows_isClosedEmbedding, h, image_empty]

end AlspachCompactRows

theorem alspachRankBound_base_le (m : ℕ) :
    (ω : Ordinal.{0}) + 1 ≤ alspachRankBound (m + 1) 0 := by
  have hm : (1 : Ordinal) ≤ ((m + 1 : ℕ) : Ordinal) := by exact_mod_cast Nat.succ_pos m
  have hh : (ω : Ordinal) ≤ ω * ((m + 1 : ℕ) : Ordinal) := by
    simpa using (mul_le_mul_left' hm (ω : Ordinal))
  unfold alspachRankBound
  exact (add_le_add_right hh 1).trans (add_le_add_left (by norm_num) _)

variable {𝕜 B : Type*} [RCLike 𝕜] [TopologicalSpace B]
  [CompactSpace B] [T2Space B] [Countable B] (p : B)

theorem alspachFinite_wolfe_bound
    (hB : ordinalDerived (univ : Set B) ((ω : Ordinal.{0}) + 1) = ∅)
    (m : ℕ) : ∀ ε : ℝ, 1 < (2 : ℝ) ^ m * ε → ∀ n : ℕ,
      wolfeFamily (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).pointAtomicModel ε
        (range (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).weakRows) (alspachRankBound m n) = ∅ := by
  induction m with
  | zero =>
      intro ε hε n
      exact (alspachFiniteCompactRows B p n).wolfe_empty_of_one_lt (by simpa using hε) _
  | succ m ihm =>
      intro ε hpow n
      have hε : 0 < ε := (mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0 : ℝ) < 2) (m + 1))).mp
        (lt_trans zero_lt_one hpow)
      induction n with
      | zero =>
          apply (AlspachCompactRows.base (𝕜 := 𝕜) B p).wolfe_empty_mono
            (alspachRankBound_countable (m + 1) 0) (alspachRankBound_base_le m)
          exact (AlspachCompactRows.base (𝕜 := 𝕜) B p).wolfe_empty_of_index_rank hε _ hB
      | succ n ihn =>
          have hd : 1 < (2 : ℝ) ^ m * (2 * ε) := by
            simpa only [pow_succ, mul_assoc] using hpow
          have he := AlspachCompactRows.successor_wolfe_empty p
            (alspachFiniteCompactRows (𝕜 := 𝕜) B p n) hε
            (alspachRankBound (m + 1) n) (alspachRankBound m n) (ω + 1)
            (alspachRankBound (m + 1) n) (alspachRankBound_countable (m + 1) n)
            le_rfl (by simpa only [← add_assoc] using alspachRankBound_add_omega_add_one m n)
            hB ihn (ihm (2 * ε) hd n)
          apply (alspachFiniteCompactRows (𝕜 := 𝕜) B p (n + 1)).wolfe_empty_mono
            (alspachRankBound_countable (m + 1) (n + 1))
            (alspachRankBound_add_two (m + 1) n)
          simpa only [← Ordinal.add_one_eq_succ, add_assoc, one_add_one_eq_two] using he

end Posets
