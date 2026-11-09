import CKEUPFP.MainStatements
import CKEUPFP.CantorExtension

/-! The disjoint clopen shells of binary Cantor space. Shell `n` consists
of sequences whose first `1` occurs in position `n`. Each shell is a copy
of the entire Cantor space, and the shells converge uniformly to zero. -/

noncomputable section

namespace CKEUPFP

def cantorShellEmbedding (n : ℕ) : C(CantorSpace, CantorSpace) :=
  ⟨fun x k => if k < n then 0 else if k = n then 1 else x (k - (n + 1)), by
    apply continuous_pi
    intro k
    by_cases hkn : k < n
    · simpa only [if_pos hkn] using (continuous_const : Continuous (fun _ : CantorSpace => (0 : Fin 2)))
    · by_cases hke : k = n
      · simpa only [if_neg hkn, if_pos hke] using
          (continuous_const : Continuous (fun _ : CantorSpace => (1 : Fin 2)))
      · simpa only [if_neg hkn, if_neg hke] using continuous_apply (k - (n + 1))⟩

def cantorShellTail (n : ℕ) : C(CantorSpace, CantorSpace) :=
  ⟨fun x k => x (k + (n + 1)), continuous_pi (fun k => continuous_apply (k + (n + 1)))⟩

@[simp] theorem cantorShellTail_embedding (n : ℕ) (x : CantorSpace) :
    cantorShellTail n (cantorShellEmbedding n x) = x := by
  funext k
  change (if k + (n + 1) < n then 0 else
    if k + (n + 1) = n then 1 else x (k + (n + 1) - (n + 1))) = x k
  simp only [if_neg (show ¬ k + (n + 1) < n by omega),
    if_neg (show k + (n + 1) ≠ n by omega), Nat.add_sub_cancel]

def cantorShellPrefix (n : ℕ) : C(CantorSpace, (Fin n → Fin 2) × Fin 2) :=
  ⟨fun x => (fun k => x k.val, x n),
    (continuous_pi (fun k => continuous_apply k.val)).prodMk (continuous_apply n)⟩

def cantorShell (n : ℕ) : Set CantorSpace :=
  cantorShellPrefix n ⁻¹' {((0 : Fin n → Fin 2), (1 : Fin 2))}

theorem mem_cantorShell_iff (n : ℕ) (x : CantorSpace) :
    x ∈ cantorShell n ↔ (∀ k, k < n → x k = 0) ∧ x n = 1 := by
  change (fun k : Fin n => x k.val, x n) = (0, 1) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨?_, hn⟩
    intro k hk
    exact congrFun h ⟨k, hk⟩
  · rintro ⟨h, hn⟩
    refine ⟨?_, hn⟩
    funext k
    exact h k.val k.isLt

theorem isClosed_cantorShell (n : ℕ) : IsClosed (cantorShell n) :=
  isClosed_singleton.preimage (cantorShellPrefix n).continuous

theorem isOpen_cantorShell (n : ℕ) : IsOpen (cantorShell n) :=
  (isOpen_discrete _).preimage (cantorShellPrefix n).continuous

instance cantorShellCompact (n : ℕ) : CompactSpace (cantorShell n) :=
  isCompact_iff_compactSpace.mp (isClosed_cantorShell n).isCompact

theorem cantorShellEmbedding_mem (n : ℕ) (x : CantorSpace) :
    cantorShellEmbedding n x ∈ cantorShell n := by
  rw [mem_cantorShell_iff]
  constructor
  · intro k hk
    change (if k < n then 0 else if k = n then 1 else _) = 0
    simp only [if_pos hk]
  · change (if n < n then 0 else if n = n then 1 else _) = 1
    simp

theorem cantorShell_nonempty (n : ℕ) : (cantorShell n).Nonempty :=
  ⟨cantorShellEmbedding n 0, cantorShellEmbedding_mem n 0⟩

theorem zero_not_mem_cantorShell (n : ℕ) : (0 : CantorSpace) ∉ cantorShell n := by
  intro h
  have h' := (mem_cantorShell_iff n 0).1 h
  exact Fin.zero_ne_one h'.2

theorem cantorShell_disjoint {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (cantorShell m) (cantorShell n) := by
  apply Set.disjoint_left.mpr
  intro x hm hn
  rcases (mem_cantorShell_iff m x).1 hm with ⟨hm0, hm1⟩
  rcases (mem_cantorShell_iff n x).1 hn with ⟨hn0, hn1⟩
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact Fin.zero_ne_one ((hn0 m hlt).symm.trans hm1)
  · exact Fin.zero_ne_one ((hm0 n hgt).symm.trans hn1)

def cantorShellRestrictedTail (n : ℕ) : C(cantorShell n, CantorSpace) :=
  (cantorShellTail n).comp ⟨Subtype.val, continuous_subtype_val⟩

end CKEUPFP
