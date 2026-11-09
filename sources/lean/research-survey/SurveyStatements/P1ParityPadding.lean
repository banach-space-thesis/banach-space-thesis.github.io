import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Finite parity padding for the complex Rosenthal selection argument.
The unused odd positions between successive targets let arbitrary prescribed
two-valued patterns be read from an alternating finite pattern. -/

set_option autoImplicit false
namespace SurveyStatements.P1

private theorem exists_bounded_parity_padding (F D : Finset ℕ) :
    ∃ G : Finset ℕ, F.image (fun n => 2 * n + 2) ⊆ G ∧
      (∀ n ∈ F, (G.filter (fun k => k < 2 * n + 2)).card % 2 =
        (if n ∈ D then 1 else 0)) ∧
      ∀ k ∈ G, ∃ n ∈ F, k ≤ 2 * n + 2 := by
  classical
  induction F using Finset.induction_on_max with
  | h0 => exact ⟨∅, by simp, by simp, by simp⟩
  | @step n F hlt ih =>
      obtain ⟨G, hinc, hrank, hbounded⟩ := ih
      have hGbound : ∀ k ∈ G, k ≤ 2 * n := by
        intro k hk
        obtain ⟨m, hm, hkm⟩ := hbounded k hk
        have := hlt m hm
        omega
      have hpad : 2 * n + 1 ∉ G := by
        intro h
        have := hGbound _ h
        omega
      let H := if G.card % 2 = (if n ∈ D then 1 else 0) then G
        else insert (2 * n + 1) G
      have hGH : G ⊆ H := by
        dsimp [H]
        split_ifs <;> simp
      have hHbound : ∀ k ∈ H, k < 2 * n + 2 := by
        intro k hk
        by_cases hc : G.card % 2 = (if n ∈ D then 1 else 0)
        · have hkG : k ∈ G := by simpa [H, hc] using hk
          have := hGbound k hkG
          omega
        · have hk' : k = 2 * n + 1 ∨ k ∈ G := by simpa [H, hc] using hk
          rcases hk' with rfl | hkG
          · omega
          · have := hGbound k hkG
            omega
      have hcard : H.card % 2 = (if n ∈ D then 1 else 0) := by
        dsimp [H]
        by_cases hc : G.card % 2 = (if n ∈ D then 1 else 0)
        · rw [if_pos hc]
          exact hc
        · rw [if_neg hc, Finset.card_insert_of_notMem hpad]
          have := Nat.mod_lt G.card (by decide : 0 < 2)
          split_ifs at hc ⊢ <;> omega
      have hfilter (m : ℕ) (hm : m ∈ F) :
          H.filter (fun k => k < 2 * m + 2) =
            G.filter (fun k => k < 2 * m + 2) := by
        have hmn := hlt m hm
        have hnot : ¬2 * n + 1 < 2 * m + 2 := by omega
        dsimp [H]
        split_ifs <;> simp [Finset.filter_insert, hnot]
      refine ⟨insert (2 * n + 2) H, ?_, ?_, ?_⟩
      · intro k hk
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (hGH (hinc (Finset.mem_image.mpr ⟨m, hm, rfl⟩)))
      · intro m hm
        rcases Finset.mem_insert.mp hm with hmn | hm
        · subst m
          have he : (insert (2 * n + 2) H).filter (fun k => k < 2 * n + 2) = H := by
            rw [Finset.filter_insert]
            simp only [lt_self_iff_false, ↓reduceIte]
            exact Finset.filter_true_of_mem (fun k hk => hHbound k hk)
          rw [he]
          exact hcard
        · have hmn := hlt m hm
          have hnot : ¬2 * n + 2 < 2 * m + 2 := by omega
          simp only [Finset.filter_insert, if_neg hnot, hfilter m hm]
          exact hrank m hm
      · intro k hk
        refine ⟨n, Finset.mem_insert_self _ _, ?_⟩
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact le_rfl
        · exact (hHbound k hk).le

theorem exists_parity_padding (F D : Finset ℕ) (_hDF : D ⊆ F) :
    ∃ G : Finset ℕ, F.image (fun n => 2 * n + 2) ⊆ G ∧
      ∀ n ∈ F, (G.filter (fun k => k < 2 * n + 2)).card % 2 =
        (if n ∈ D then 1 else 0) := by
  obtain ⟨G, hinc, hrank, _⟩ := exists_bounded_parity_padding F D
  exact ⟨G, hinc, hrank⟩

end SurveyStatements.P1
