import SurveyStatements.P1ThinFamilyRamseyFinite

/-! For each prescribed minimum, a palette bounded by that minimum is finite.
Removing the common minimum preserves thinness, including empty tails. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace SurveyStatements.P1

theorem initialSegment_insert_min (m : ℕ) (u v : Finset ℕ)
    (huv : FinsetIsInitialSegment u v) (hmin : ∀ b ∈ v, m ≤ b) :
    FinsetIsInitialSegment (insert m u) (insert m v) := by
  refine ⟨Finset.insert_subset_insert m huv.1, ?_⟩
  intro a ha b hb hba
  have hbm : b ≠ m := fun h => hba (h ▸ Finset.mem_insert_self m u)
  have hbv : b ∈ v := (Finset.mem_insert.mp hb).resolve_left hbm
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact lt_of_le_of_ne (hmin b hbv) hbm.symm
  · exact huv.2 a ha b hbv (fun hbu => hba (Finset.mem_insert_of_mem hbu))

theorem thin_family_homogeneous_at_minimum (A : Set (Finset ℕ))
    (hA : IsThinFiniteFamily A) (hne : ∀ s ∈ A, s.Nonempty)
    (Γ : ℕ → ℕ) (c : Finset ℕ → ℕ)
    (hbound : ∀ s ∈ A, c s ≤ Γ (sInf (s : Set ℕ)))
    (m : ℕ) (M : Set ℕ) (hM : M.Infinite) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ s ∈ A, ∀ t ∈ A,
        sInf (s : Set ℕ) = m → sInf (t : Set ℕ) = m →
        (s : Set ℕ) ⊆ insert m L → (t : Set ℕ) ⊆ insert m L → c s = c t := by
  let B : Set (Finset ℕ) := {u | ∃ s ∈ A, sInf (s : Set ℕ) = m ∧ u = s.erase m}
  have hmemb (s : Finset ℕ) (hs : s ∈ A) (hsm : sInf (s : Set ℕ) = m) :
      m ∈ s := by
    rw [← hsm]
    exact Nat.sInf_mem (Finset.coe_nonempty.mpr (hne s hs))
  have hB : IsThinFiniteFamily B := by
    rintro u ⟨s, hs, hsm, rfl⟩ v ⟨t, ht, htm, rfl⟩ huv
    have hins := initialSegment_insert_min m (s.erase m) (t.erase m) huv (by
      intro b hb
      have hmin := Nat.sInf_le (show b ∈ (t : Set ℕ) from (Finset.mem_erase.mp hb).2)
      simpa only [htm] using hmin)
    rw [Finset.insert_erase (hmemb s hs hsm), Finset.insert_erase (hmemb t ht htm)] at hins
    exact congrArg (fun s : Finset ℕ => s.erase m) (hA s hs t ht hins)
  let cb (u : Finset ℕ) := c (insert m u)
  have hcb : ∀ u ∈ B, cb u ≤ Γ m := by
    rintro u ⟨s, hs, hsm, rfl⟩
    change c (insert m (s.erase m)) ≤ Γ m
    rw [Finset.insert_erase (hmemb s hs hsm)]
    simpa only [hsm] using hbound s hs
  let cf (u : Finset ℕ) : Fin (Γ m + 1) :=
    ⟨cb u % (Γ m + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  obtain ⟨L, hLM, hL, hcolor⟩ := thin_family_finiteColorRamsey B hB cf M hM
  refine ⟨L, hLM, hL, ?_⟩
  intro s hs t ht hsm htm hsL htL
  have hsB : s.erase m ∈ B := ⟨s, hs, hsm, rfl⟩
  have htB : t.erase m ∈ B := ⟨t, ht, htm, rfl⟩
  have hsL' : (s.erase m : Set ℕ) ⊆ L := by
    intro x hx
    exact (hsL (Finset.mem_of_mem_erase hx)).resolve_left (Finset.ne_of_mem_erase hx)
  have htL' : (t.erase m : Set ℕ) ⊆ L := by
    intro x hx
    exact (htL (Finset.mem_of_mem_erase hx)).resolve_left (Finset.ne_of_mem_erase hx)
  have heq := congrArg Fin.val (hcolor _ hsB _ htB hsL' htL')
  change cb (s.erase m) % (Γ m + 1) = cb (t.erase m) % (Γ m + 1) at heq
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hcb _ hsB)),
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hcb _ htB))] at heq
  simpa only [cb, Finset.insert_erase (hmemb s hs hsm),
    Finset.insert_erase (hmemb t ht htm)] using heq

end SurveyStatements.P1
