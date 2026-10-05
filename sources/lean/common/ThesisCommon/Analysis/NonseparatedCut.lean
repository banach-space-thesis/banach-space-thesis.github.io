import ThesisCommon.Analysis.AlmostDisjointFamily
import ThesisCommon.Analysis.SeparationCounting

/-! Infinite nonseparated cuts, chosen inside a prescribed infinite set. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon

theorem finitelySeparated_image_iff {D E I : Type*} (ev : E → I → ℝ)
    (f : D → E) (T : Set I) (M N : Set D) :
    FinitelySeparated ev T (f '' M) (f '' N) ↔
      FinitelySeparated (fun d i => ev (f d) i) T M N := by
  constructor
  · rintro ⟨ε, hε, F, hF, hsep⟩
    exact ⟨ε, hε, F, hF, fun m hm n hn =>
      hsep (f m) (Set.mem_image_of_mem f hm) (f n) (Set.mem_image_of_mem f hn)⟩
  · rintro ⟨ε, hε, F, hF, hsep⟩
    refine ⟨ε, hε, F, hF, ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    exact hsep m hm n hn

theorem exists_infinite_nonseparated_cut {I : Type} (ev : ℕ → I → ℝ)
    (hbound : ∀ n i, |ev n i| ≤ 1) (hI : #I < 𝔠)
    (M D : Set ℕ) (hDM : D ⊆ M) (hD : D.Infinite) :
    ∃ A : Set ℕ, A ⊆ D ∧ A.Infinite ∧ (D \ A).Infinite ∧
      ¬ FinitelySeparated ev Set.univ A (M \ A) := by
  classical
  obtain ⟨S, hcard, hsub, hAD⟩ := continuum_almostDisjoint_subsets D hD
  let bad : Set (Set ℕ) := {A | A ⊆ M ∧ FinitelySeparated ev Set.univ A (M \ A)}
  have hbad : #bad < 𝔠 := separated_cuts_lt_continuum ev hbound M hI
  have hnot : ¬ S ⊆ bad := by
    intro h
    have hle := Cardinal.mk_le_mk_of_subset h
    rw [hcard] at hle
    exact (not_le_of_gt hbad) hle
  obtain ⟨A, hAS, hAnot⟩ := Set.not_subset.mp hnot
  have hSinf : S.Infinite := by
    intro hSfin
    haveI : Finite S := hSfin
    have hh : #S < ℵ₀ := Cardinal.mk_lt_aleph0
    rw [hcard] at hh
    exact (not_lt_of_ge Cardinal.aleph0_le_continuum) hh
  obtain ⟨B, hBS, hBA⟩ := hSinf.exists_notMem_finset {A}
  have hBA' : B ≠ A := by simpa using hBA
  have hinf : (B \ (B ∩ A)).Infinite := (hsub B hBS).2.diff (hAD hBS hAS hBA')
  have hdiff : (D \ A).Infinite := hinf.mono (by
    intro x hx
    refine ⟨(hsub B hBS).1 hx.1, ?_⟩
    intro hxa
    exact hx.2 ⟨hx.1, hxa⟩)
  exact ⟨A, (hsub A hAS).1, (hsub A hAS).2, hdiff,
    fun hsep => hAnot ⟨(hsub A hAS).1.trans hDM, hsep⟩⟩

end ThesisCommon
