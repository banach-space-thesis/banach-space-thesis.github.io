import Posets.PaperChainCatalanMaps

/-! Splitting an extensive monotone map at its first fixed point is a
bijection with a pair of smaller maps. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets

def paperCatalanLeft {n : ℕ} (f : PaperCatalanMap (n + 1)) :
    PaperCatalanMap (paperCatalanFirstFixed f).val := by
  let r := paperCatalanFirstFixed f
  have hl (i : Fin r.val) : i.val < (f.val ⟨i.val, by omega⟩).val :=
    paperCatalan_lt_before_fixed f ⟨i.val, by omega⟩ i.isLt
  have hu (i : Fin r.val) : (f.val ⟨i.val, by omega⟩).val ≤ r.val := by
    have h := f.property.1 (show (⟨i.val, by omega⟩ : Fin (n + 1)) ≤ r from i.isLt.le)
    rw [paperCatalanFirstFixed_fixed] at h
    exact h
  refine ⟨fun i => ⟨(f.val ⟨i.val, by omega⟩).val - 1, by have := hl i; have := hu i; omega⟩,
    ?_, ?_⟩
  · intro i j hij
    have h : (f.val ⟨i.val, by omega⟩).val ≤ (f.val ⟨j.val, by omega⟩).val := f.property.1 hij
    change _ - 1 ≤ _ - 1
    omega
  · intro i
    change i.val ≤ _ - 1
    have := hl i
    omega

def paperCatalanRight {n : ℕ} (f : PaperCatalanMap (n + 1)) :
    PaperCatalanMap (n - (paperCatalanFirstFixed f).val) := by
  let r := paperCatalanFirstFixed f
  let k (i : Fin (n - r.val)) : Fin (n + 1) := ⟨r.val + 1 + i.val, by omega⟩
  have hl (i : Fin (n - r.val)) : r.val + 1 + i.val ≤ (f.val (k i)).val := f.property.2 (k i)
  refine ⟨fun i => ⟨(f.val (k i)).val - r.val - 1, by
    have := (f.val (k i)).isLt; have := hl i; omega⟩, ?_, ?_⟩
  · intro i j hij
    have h : (f.val (k i)).val ≤ (f.val (k j)).val := f.property.1 (by
      change r.val + 1 + i.val ≤ r.val + 1 + j.val
      exact Nat.add_le_add_left hij _)
    change _ - r.val - 1 ≤ _ - r.val - 1
    omega
  · intro i
    change i.val ≤ _ - r.val - 1
    have := hl i
    omega

def paperCatalanSplit {n : ℕ} (f : PaperCatalanMap (n + 1)) :
    Σ r : Fin (n + 1), PaperCatalanMap r.val × PaperCatalanMap (n - r.val) :=
  ⟨paperCatalanFirstFixed f, paperCatalanLeft f, paperCatalanRight f⟩

theorem paperCatalanJoin_split {n : ℕ} (f : PaperCatalanMap (n + 1)) :
    paperCatalanJoin (paperCatalanFirstFixed f) (paperCatalanLeft f) (paperCatalanRight f) = f := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  let r := paperCatalanFirstFixed f
  change paperCatalanJoinValue r (paperCatalanLeft f) (paperCatalanRight f) i = (f.val i).val
  unfold paperCatalanJoinValue
  split_ifs with hi hir
  · have h : i.val < (f.val i).val := paperCatalan_lt_before_fixed f i hi
    simp only [paperCatalanLeft]
    have he : (⟨i.val, by omega⟩ : Fin (n + 1)) = i := Fin.ext rfl
    simp only [he]
    omega
  · have he : i = r := Fin.ext hir
    rw [he]
    exact congrArg Fin.val (paperCatalanFirstFixed_fixed f).symm
  · simp only [paperCatalanRight]
    change r.val + 1 + ((f.val ⟨r.val + 1 + (i.val - r.val - 1), by omega⟩).val -
      r.val - 1) = (f.val i).val
    have he : (⟨r.val + 1 + (i.val - r.val - 1), by omega⟩ : Fin (n + 1)) = i := by
      apply Fin.ext
      change r.val + 1 + (i.val - r.val - 1) = i.val
      omega
    rw [he]
    have h : i.val ≤ (f.val i).val := f.property.2 i
    omega

theorem paperCatalanFirstFixed_join {n : ℕ} (r : Fin (n + 1))
    (a : PaperCatalanMap r.val) (b : PaperCatalanMap (n - r.val)) :
    paperCatalanFirstFixed (paperCatalanJoin r a b) = r := by
  have hfix : (paperCatalanJoin r a b).val r = r := by
    apply Fin.ext
    simp [paperCatalanJoin, paperCatalanJoinValue]
  apply le_antisymm (paperCatalanFirstFixed_le _ r hfix)
  by_contra hn
  have hi : (paperCatalanFirstFixed (paperCatalanJoin r a b)).val < r.val := lt_of_not_ge hn
  have hf := congrArg Fin.val (paperCatalanFirstFixed_fixed (paperCatalanJoin r a b))
  change paperCatalanJoinValue r a b (paperCatalanFirstFixed (paperCatalanJoin r a b)) = _ at hf
  rw [paperCatalanJoinValue, dif_pos hi] at hf
  have ha := a.property.2 ⟨_, hi⟩
  change (paperCatalanFirstFixed (paperCatalanJoin r a b)).val ≤ (a.val ⟨_, hi⟩).val at ha
  omega

theorem paperCatalanJoin_injective (n : ℕ) : Function.Injective
    (fun x : Σ r : Fin (n + 1), PaperCatalanMap r.val × PaperCatalanMap (n - r.val) =>
      paperCatalanJoin x.1 x.2.1 x.2.2) := by
  rintro ⟨r, a, b⟩ ⟨s, c, d⟩ h
  have hrs : r = s := by
    have hh := congrArg paperCatalanFirstFixed h
    simpa only [paperCatalanFirstFixed_join] using hh
  cases hrs
  have hac : a = c := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh := congrArg (fun f : PaperCatalanMap (n + 1) => (f.val ⟨i.val, by omega⟩).val) h
    change paperCatalanJoinValue r a b ⟨i.val, by omega⟩ =
      paperCatalanJoinValue r c d ⟨i.val, by omega⟩ at hh
    simp only [paperCatalanJoinValue, dif_pos i.isLt] at hh
    change (a.val i).val + 1 = (c.val i).val + 1 at hh
    omega
  have hbd : b = d := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh := congrArg (fun f : PaperCatalanMap (n + 1) =>
      (f.val ⟨r.val + 1 + i.val, by omega⟩).val) h
    change paperCatalanJoinValue r a b ⟨r.val + 1 + i.val, by omega⟩ =
      paperCatalanJoinValue r c d ⟨r.val + 1 + i.val, by omega⟩ at hh
    have hnot : ¬ r.val + 1 + i.val < r.val := by omega
    have hne : r.val + 1 + i.val ≠ r.val := by omega
    simp only [paperCatalanJoinValue, dif_neg hnot, dif_neg hne] at hh
    have he : (⟨r.val + 1 + i.val - r.val - 1, by omega⟩ : Fin (n - r.val)) = i := by
      apply Fin.ext
      change r.val + 1 + i.val - r.val - 1 = i.val
      omega
    rw [he] at hh
    omega
  cases hac
  cases hbd
  rfl

def paperCatalanSplitEquiv (n : ℕ) : PaperCatalanMap (n + 1) ≃
    Σ r : Fin (n + 1), PaperCatalanMap r.val × PaperCatalanMap (n - r.val) where
  toFun := paperCatalanSplit
  invFun x := paperCatalanJoin x.1 x.2.1 x.2.2
  left_inv := paperCatalanJoin_split
  right_inv _ := paperCatalanJoin_injective n (paperCatalanJoin_split _)

theorem paperCatalanMap_card (n : ℕ) : Fintype.card (PaperCatalanMap n) = catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      haveI : Unique (PaperCatalanMap 0) :=
        ⟨⟨⟨id, monotone_id, fun _ => le_rfl⟩⟩, fun f => Subtype.ext (Subsingleton.elim _ _)⟩
      simp
    | succ n =>
      rw [Fintype.card_congr (paperCatalanSplitEquiv n), Fintype.card_sigma, catalan_succ]
      apply Finset.sum_congr rfl
      intro r _
      rw [Fintype.card_prod, ih r.val r.isLt, ih (n - r.val) (by omega)]

end Posets
