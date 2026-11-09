import SurveyStatements.P1ThinFamilyRamseyMinimum

/-! Thin-family homogeneity with finite palettes depending on the least support
index. Each fusion step fixes its actual next least index before refining. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace SurveyStatements.P1

theorem thin_family_boundedColorRamsey (A : Set (Finset ℕ))
    (hA : IsThinFiniteFamily A) (hne : ∀ s ∈ A, s.Nonempty)
    (Γ : ℕ → ℕ) (c : Finset ℕ → ℕ)
    (hbound : ∀ s ∈ A, c s ≤ Γ (sInf (s : Set ℕ)))
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ N : Set ℕ, N ⊆ M ∧ N.Infinite ∧
      ∀ s ∈ A, ∀ t ∈ A, (s : Set ℕ) ⊆ N → (t : Set ℕ) ⊆ N →
        sInf (s : Set ℕ) = sInf (t : Set ℕ) → c s = c t := by
  let Ω := {L : Set ℕ // L.Infinite}
  have hstep (q : Ω) : ∃ L : Set ℕ,
      L ⊆ q.val ∩ Ioi (sInf q.val) ∧ L.Infinite ∧
      ∀ s ∈ A, ∀ t ∈ A,
        sInf (s : Set ℕ) = sInf q.val →
        sInf (t : Set ℕ) = sInf q.val →
        (s : Set ℕ) ⊆ insert (sInf q.val) L →
        (t : Set ℕ) ⊆ insert (sInf q.val) L → c s = c t :=
    thin_family_homogeneous_at_minimum A hA hne Γ c hbound (sInf q.val)
      (q.val ∩ Ioi (sInf q.val)) (infiniteSet_inter_Ioi q.val q.property _)
  choose nextSet nextSub nextInf nextHom using hstep
  let next (q : Ω) : Ω := ⟨nextSet q, nextInf q⟩
  let q : ℕ → Ω := Nat.rec ⟨M, hM⟩ (fun _ q => next q)
  let μ (n : ℕ) := sInf (q n).val
  have hmem (n : ℕ) : μ n ∈ (q n).val := Nat.sInf_mem (q n).property.nonempty
  have hnext (n : ℕ) : (q (n + 1)).val ⊆ (q n).val ∩ Ioi (μ n) :=
    nextSub (q n)
  have hμ : StrictMono μ := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (hnext n (hmem (n + 1))).2
  have hanti : Antitone (fun n => (q n).val) :=
    antitone_nat_of_succ_le (fun n x hx => (hnext n hx).1)
  refine ⟨range μ, ?_, Set.infinite_range_of_injective hμ.injective, ?_⟩
  · rintro x ⟨n, rfl⟩
    exact hanti (Nat.zero_le n) (hmem n)
  · intro s hs t ht hsN htN hst
    have hsmin : sInf (s : Set ℕ) ∈ s :=
      Nat.sInf_mem (Finset.coe_nonempty.mpr (hne s hs))
    obtain ⟨r, hr⟩ := hsN hsmin
    have hsminr : sInf (s : Set ℕ) = μ r := hr.symm
    have htminr : sInf (t : Set ℕ) = μ r := hst.symm.trans hsminr
    have hsupport (u : Finset ℕ) (huN : (u : Set ℕ) ⊆ range μ)
        (hum : sInf (u : Set ℕ) = μ r) :
        (u : Set ℕ) ⊆ insert (μ r) (q (r + 1)).val := by
      intro x hx
      obtain ⟨j, rfl⟩ := huN hx
      by_cases hj : j = r
      · exact Or.inl (congrArg μ hj)
      · right
        have hmin := Nat.sInf_le (show μ j ∈ (u : Set ℕ) from hx)
        rw [hum] at hmin
        have hrj : r < j := lt_of_le_of_ne (hμ.le_iff_le.mp hmin) (Ne.symm hj)
        exact hanti (Nat.succ_le_of_lt hrj) (hmem j)
    exact nextHom (q r) s hs t ht hsminr htminr
      (hsupport s hsN hsminr) (hsupport t htN htminr)

end SurveyStatements.P1
