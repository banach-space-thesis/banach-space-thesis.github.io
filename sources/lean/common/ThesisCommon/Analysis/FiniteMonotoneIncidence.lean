import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! A noncrossing family of pairs of finite ordered indices has at most
the sum of the two index counts. The rank i+j is an actual injection. -/
namespace ThesisCommon

theorem card_monotone_incidence_le {N m : ℕ} (s : Finset (Fin N × Fin m))
    (h : ∀ a ∈ s, ∀ b ∈ s, a.1 < b.1 → a.2 ≤ b.2) : s.card ≤ N + m := by
  classical
  have hc : s.card ≤ (Finset.range (N + m)).card := by
    apply Finset.card_le_card_of_injOn (fun a : Fin N × Fin m => a.1.val + a.2.val)
    · intro a _
      apply Finset.mem_range.mpr
      change a.1.val + a.2.val < N + m
      have h1 := a.1.isLt
      have h2 := a.2.isLt
      omega
    · intro a ha b hb heq
      change a.1.val + a.2.val = b.1.val + b.2.val at heq
      rcases lt_trichotomy a.1 b.1 with hlt | heq1 | hgt
      · have hs := h a ha b hb hlt
        have hf : a.1.val < b.1.val := hlt
        have hsec : a.2.val ≤ b.2.val := hs
        omega
      · apply Prod.ext heq1
        apply Fin.ext
        have hf : a.1.val = b.1.val := congrArg Fin.val heq1
        omega
      · have hs := h b hb a ha hgt
        have hf : b.1.val < a.1.val := hgt
        have hsec : b.2.val ≤ a.2.val := hs
        omega
  simpa using hc

end ThesisCommon
