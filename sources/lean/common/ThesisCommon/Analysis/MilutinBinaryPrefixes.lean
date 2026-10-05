import ThesisCommon.Analysis.MilutinBinaryEmbedding

/-! Finite-prefix lemmas used to construct a continuous retraction onto a
nonempty closed subset of the actual binary Cantor space. -/

noncomputable section
open Set Filter Topology
namespace ThesisCommon

def milutinBinaryPrefix (x : ℕ → Bool) (n : ℕ) : Fin n → Bool := fun i => x i

def MilutinPrefixCompatible (C : Set (ℕ → Bool)) (x : ℕ → Bool) (n : ℕ) : Prop :=
  ∃ z : C, ∀ k < n, z.val k = x k

theorem milutinPrefixCompatible_zero (C : Set (ℕ → Bool)) (hC : C.Nonempty) (x : ℕ → Bool) :
    MilutinPrefixCompatible C x 0 := ⟨⟨hC.some, hC.some_mem⟩, by omega⟩

theorem MilutinPrefixCompatible.mono {C : Set (ℕ → Bool)} {x : ℕ → Bool} {n m : ℕ}
    (h : MilutinPrefixCompatible C x n) (hmn : m ≤ n) : MilutinPrefixCompatible C x m := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, fun k hk => hz k (lt_of_lt_of_le hk hmn)⟩

theorem milutinPrefixCompatible_congr {C : Set (ℕ → Bool)} {x y : ℕ → Bool} {n : ℕ}
    (hxy : ∀ k < n, x k = y k) :
    MilutinPrefixCompatible C x n ↔ MilutinPrefixCompatible C y n := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, fun k hk => (hz k hk).trans (hxy k hk)⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, fun k hk => (hz k hk).trans (hxy k hk).symm⟩

theorem milutinBinaryCylinder_mem_nhds (x : ℕ → Bool) (n : ℕ) :
    {y : ℕ → Bool | ∀ k < n, y k = x k} ∈ 𝓝 x := by
  have hc : Continuous (fun y : ℕ → Bool => milutinBinaryPrefix y n) :=
    continuous_pi fun i => continuous_apply i.val
  have h := hc.continuousAt.preimage_mem_nhds
    ((isOpen_discrete (s := {milutinBinaryPrefix x n})).mem_nhds (mem_singleton _))
  convert h using 1
  ext y
  simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, funext_iff, milutinBinaryPrefix]
  exact ⟨fun hy i => hy i i.isLt, fun hy k hk => hy ⟨k, hk⟩⟩

theorem milutinBinary_exists_incompatible (C : Set (ℕ → Bool)) (hclosed : IsClosed C)
    (x : ℕ → Bool) (hx : x ∉ C) : ∃ n, ¬ MilutinPrefixCompatible C x (n + 1) := by
  classical
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hclosed.isOpen_compl x hx
  refine ⟨I.sup id, ?_⟩
  rintro ⟨z, hz⟩
  apply hsub ?_ z.property
  intro k hk
  rw [hz k (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))]
  exact (hu k hk).2

def milutinBinaryExit (C : Set (ℕ → Bool)) (hclosed : IsClosed C)
    (x : ℕ → Bool) (hx : x ∉ C) : ℕ := by
  classical
  exact Nat.find (milutinBinary_exists_incompatible C hclosed x hx)

theorem milutinBinaryExit_bad (C : Set (ℕ → Bool)) (hclosed : IsClosed C)
    (x : ℕ → Bool) (hx : x ∉ C) :
    ¬ MilutinPrefixCompatible C x (milutinBinaryExit C hclosed x hx + 1) := by
  classical
  exact Nat.find_spec (milutinBinary_exists_incompatible C hclosed x hx)

theorem milutinBinaryExit_compatible (C : Set (ℕ → Bool)) (hC : C.Nonempty)
    (hclosed : IsClosed C) (x : ℕ → Bool) (hx : x ∉ C) :
    MilutinPrefixCompatible C x (milutinBinaryExit C hclosed x hx) := by
  classical
  by_cases hn : milutinBinaryExit C hclosed x hx = 0
  · rw [hn]
    exact milutinPrefixCompatible_zero C hC x
  · have hpos : 1 ≤ milutinBinaryExit C hclosed x hx := Nat.one_le_iff_ne_zero.mpr hn
    have hlt : milutinBinaryExit C hclosed x hx - 1 < milutinBinaryExit C hclosed x hx := by omega
    have h := Nat.find_min (milutinBinary_exists_incompatible C hclosed x hx) hlt
    have hc := Classical.not_not.mp h
    simpa only [Nat.sub_add_cancel hpos] using hc

def milutinBinaryPrefixChoice (C : Set (ℕ → Bool)) (hC : C.Nonempty)
    (n : ℕ) (w : Fin n → Bool) : C := by
  classical
  exact if h : ∃ z : C, ∀ i : Fin n, z.val i = w i then h.choose else ⟨hC.some, hC.some_mem⟩

theorem milutinBinaryPrefixChoice_eq (C : Set (ℕ → Bool)) (hC : C.Nonempty)
    (x : ℕ → Bool) (n : ℕ) (h : MilutinPrefixCompatible C x n) :
    ∀ k < n, (milutinBinaryPrefixChoice C hC n (milutinBinaryPrefix x n)).val k = x k := by
  classical
  have hw : ∃ z : C, ∀ i : Fin n, z.val i = milutinBinaryPrefix x n i := by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, fun i => hz i i.isLt⟩
  intro k hk
  simp only [milutinBinaryPrefixChoice, dif_pos hw]
  exact hw.choose_spec ⟨k, hk⟩

end ThesisCommon
