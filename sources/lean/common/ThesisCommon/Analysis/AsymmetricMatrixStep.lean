import ThesisCommon.Analysis.AsymmetricMatrixSelection

/-! The extension step of the asymmetric pair-indexed selection: exclude
finitely many incoming large coordinates, apply simultaneous infinite
pigeonhole, and cut tails in the retained reservoirs.
-/
noncomputable section
open scoped Classical BigOperators
namespace ThesisCommon
namespace AsymmetricMatrixSelection
variable {w : (ℕ × ℕ) → (ℕ × ℕ) → ℝ} {δ : (ℕ × ℕ) → ℕ → ℝ}

theorem step (hδ : ∀ p i, 0 < δ p i)
    (hrow : ∀ p ε, 0 < ε → {i | ∃ j, ε ≤ w p (i, j)}.Finite)
    (hcol : ∀ p ε, 0 < ε → {q | ε ≤ w q p}.Finite)
    (C : ℕ → ℕ → ℝ)
    (hbound : ∀ r i j (F : Finset ℕ), ∑ s ∈ F, w (r, s) (i, j) ≤ C r i)
    {t : ℕ} (S : State w δ t) :
    ∃ U : State w δ (t + 1),
      (∀ i, index (i, 0) < t → U.row i = S.row i) ∧
      (∀ p, index p < t → U.col p = S.col p) := by
  classical
  obtain ⟨n, H, hn, hmono, hHinf, htail, hfuture⟩ := open_row hδ hrow S
  let p := Nat.unpair t
  have hp : index p = t := Nat.pair_unpair t
  have hkp : index (p.1, 0) < t + 1 := (index_zero_le p.1 p.2).trans_lt
    (by simpa only [Prod.eta, hp] using Nat.lt_succ_self t)
  have hcases (q : ℕ × ℕ) (hq : index q < t + 1) : index q < t ∨ q = p := by
    by_cases hh : index q < t
    · exact Or.inl hh
    · right
      exact Nat.pairEquiv.injective (by change index q = index p; omega)
  let bad : Set ℕ := ⋃ q ∈ {q : ℕ × ℕ | index q < t},
    {s | δ p q.1 ≤ w (n p.1, s) (n q.1, S.col q)}
  have hbad : bad.Finite := by
    apply (finite_past t).biUnion
    intro q _
    exact (hcol (n q.1, S.col q) (δ p q.1) (hδ p q.1)).preimage
      (f := fun s : ℕ => (n p.1, s))
      (fun _ _ _ _ h => (Prod.mk.inj h).2)
  let R := H p.1 \ bad
  have hR : R.Infinite := (hHinf p.1 hkp).diff hbad
  let K := (finite_active (t + 1)).toFinset
  obtain ⟨s, hsR, hs⟩ := (bounded_columns_simultaneous_small_rows
    (fun i s j => w (n p.1, s) (n i, j)) (fun i => C (n p.1) (n i)) (δ p)
    (fun i j F => hbound (n p.1) (n i) j F) (hδ p) K H hR
    (fun i hi => hHinf i ((finite_active (t + 1)).mem_toFinset.mp hi))).nonempty
  have hsource (q : ℕ × ℕ) (hq : index q < t) :
      w (n p.1, s) (n q.1, S.col q) ≤ δ p q.1 := by
    by_contra hh
    apply hsR.2
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, le_of_not_ge hh⟩⟩
  let c := Function.update S.col p s
  have hc (q : ℕ × ℕ) (hq : index q < t) : c q = S.col q := by
    apply Function.update_of_ne
    intro heq
    rw [heq, hp] at hq
    omega
  have hcp : c p = s := Function.update_self _ _ _
  let M := fun i => {v ∈ H i | w (n p.1, s) (n i, v) < δ p i ∧ s < v}
  have hMinf (i : ℕ) (hi : index (i, 0) < t + 1) : (M i).Infinite := by
    have hh := infinite_above (hs i ((finite_active (t + 1)).mem_toFinset.mpr hi)) s
    convert hh using 1
    ext v
    simp only [M, Set.mem_setOf_eq, and_assoc]
  have hMsub (i : ℕ) : M i ⊆ H i := fun _ hv => hv.1
  have holdrow (q : ℕ × ℕ) (hq : index q < t) : n q.1 = S.row q.1 :=
    hn q.1 ((index_zero_le q.1 q.2).trans_lt hq)
  let U : State w δ (t + 1) := {
    row := n
    col := c
    reservoir := M
    row_mono := hmono
    infinite := hMinf
    col_mono := by
      intro q r hq hr hqr hlt
      rcases hcases q hq with hq | rfl
      · rw [hc q hq]
        rcases hcases r hr with hr | rfl
        · rw [hc r hr]; exact S.col_mono q r hq hr hqr hlt
        · rw [hcp]
          apply htail q hq s
          rw [hqr]
          exact hsR.1
      · rcases hcases r hr with hr | rfl
        · have hh := Nat.pair_lt_pair_right p.1 hlt
          change index p < Nat.pair p.1 r.2 at hh
          rw [hqr] at hh
          change index p < index r at hh
          omega
        · exact (lt_irrefl _ hlt).elim
    tail := by
      intro q hq v hv
      rcases hcases q hq with hq | rfl
      · rw [hc q hq]
        exact htail q hq v (hMsub q.1 hv)
      · rw [hcp]; exact hv.2.2
    small := by
      intro q r hq hr hne
      rcases hcases q hq with hq | rfl
      · rw [hc q hq]
        rcases hcases r hr with hr | rfl
        · rw [hc r hr, holdrow q hq, holdrow r hr]
          exact S.small q r hq hr hne
        · rw [hcp]
          exact hfuture q hq p.1 hkp s hsR.1
      · rw [hcp]
        rcases hcases r hr with hr | rfl
        · rw [hc r hr]; exact hsource r hr
        · exact (hne rfl).elim
    future := by
      intro q hq i hi v hv
      rcases hcases q hq with hq | rfl
      · rw [hc q hq]
        exact hfuture q hq i hi v (hMsub i hv)
      · rw [hcp]
        exact hv.2.1.le }
  exact ⟨U, hn, hc⟩

end AsymmetricMatrixSelection
end ThesisCommon
