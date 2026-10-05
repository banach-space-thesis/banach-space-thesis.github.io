import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic

/-! Monotone extensive maps encode the boundary of an interval upset in a
finite chain. Their least fixed point gives the Catalan decomposition. -/

noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets

abbrev PaperCatalanMap (n : ℕ) :=
  {f : Fin n → Fin n // Monotone f ∧ ∀ i, i ≤ f i}

def paperCatalanJoinValue {n : ℕ} (r : Fin (n + 1))
    (a : PaperCatalanMap r.val) (b : PaperCatalanMap (n - r.val)) (i : Fin (n + 1)) : ℕ :=
  if h : i.val < r.val then (a.val ⟨i.val, h⟩).val + 1
  else if he : i.val = r.val then r.val
  else r.val + 1 + (b.val ⟨i.val - r.val - 1, by omega⟩).val

theorem paperCatalanJoinValue_lt {n : ℕ} (r : Fin (n + 1))
    (a : PaperCatalanMap r.val) (b : PaperCatalanMap (n - r.val)) (i : Fin (n + 1)) :
    paperCatalanJoinValue r a b i < n + 1 := by
  unfold paperCatalanJoinValue
  split_ifs with h he
  · have := (a.val ⟨i.val, h⟩).isLt
    omega
  · exact r.isLt
  · have := (b.val ⟨i.val - r.val - 1, by omega⟩).isLt
    omega

theorem paperCatalanJoinValue_extensive {n : ℕ} (r : Fin (n + 1))
    (a : PaperCatalanMap r.val) (b : PaperCatalanMap (n - r.val)) (i : Fin (n + 1)) :
    i.val ≤ paperCatalanJoinValue r a b i := by
  unfold paperCatalanJoinValue
  split_ifs with h he
  · have := a.property.2 ⟨i.val, h⟩
    change i.val ≤ (a.val ⟨i.val, h⟩).val at this
    omega
  · omega
  · have := b.property.2 ⟨i.val - r.val - 1, by omega⟩
    change i.val - r.val - 1 ≤ (b.val ⟨i.val - r.val - 1, by omega⟩).val at this
    omega

theorem paperCatalanJoinValue_monotone {n : ℕ} (r : Fin (n + 1))
    (a : PaperCatalanMap r.val) (b : PaperCatalanMap (n - r.val)) :
    Monotone (paperCatalanJoinValue r a b) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  by_cases hi : i.val < r.val
  · by_cases hj : j.val < r.val
    · simp only [paperCatalanJoinValue, dif_pos hi, dif_pos hj]
      have h : (a.val ⟨i.val, hi⟩).val ≤ (a.val ⟨j.val, hj⟩).val :=
        a.property.1 hij'
      omega
    · simp only [paperCatalanJoinValue, dif_pos hi, dif_neg hj]
      have ha := (a.val ⟨i.val, hi⟩).isLt
      split_ifs <;> omega
  · have hj : ¬ j.val < r.val := by omega
    simp only [paperCatalanJoinValue, dif_neg hi, dif_neg hj]
    split_ifs with hir hjr hjr
    · omega
    · omega
    · omega
    · have hle : i.val - r.val - 1 ≤ j.val - r.val - 1 := by omega
      have h : (b.val ⟨i.val - r.val - 1, by omega⟩).val ≤
          (b.val ⟨j.val - r.val - 1, by omega⟩).val := b.property.1 hle
      omega

def paperCatalanJoin {n : ℕ} (r : Fin (n + 1))
    (a : PaperCatalanMap r.val) (b : PaperCatalanMap (n - r.val)) : PaperCatalanMap (n + 1) :=
  ⟨fun i => ⟨paperCatalanJoinValue r a b i, paperCatalanJoinValue_lt r a b i⟩,
    paperCatalanJoinValue_monotone r a b, paperCatalanJoinValue_extensive r a b⟩

def paperCatalanFixedPoints {n : ℕ} (f : PaperCatalanMap (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => f.val i = i)

theorem paperCatalanFixedPoints_nonempty {n : ℕ} (f : PaperCatalanMap (n + 1)) :
    (paperCatalanFixedPoints f).Nonempty := by
  refine ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact le_antisymm (Fin.le_last _) (f.property.2 _)

def paperCatalanFirstFixed {n : ℕ} (f : PaperCatalanMap (n + 1)) : Fin (n + 1) :=
  (paperCatalanFixedPoints f).min' (paperCatalanFixedPoints_nonempty f)

theorem paperCatalanFirstFixed_fixed {n : ℕ} (f : PaperCatalanMap (n + 1)) :
    f.val (paperCatalanFirstFixed f) = paperCatalanFirstFixed f := by
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (paperCatalanFixedPoints f) (paperCatalanFixedPoints_nonempty f))).2

theorem paperCatalanFirstFixed_le {n : ℕ} (f : PaperCatalanMap (n + 1))
    (i : Fin (n + 1)) (hi : f.val i = i) : paperCatalanFirstFixed f ≤ i := by
  exact Finset.min'_le (paperCatalanFixedPoints f) i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

theorem paperCatalan_lt_before_fixed {n : ℕ} (f : PaperCatalanMap (n + 1))
    (i : Fin (n + 1)) (hi : i < paperCatalanFirstFixed f) : i < f.val i := by
  apply lt_of_le_of_ne (f.property.2 i)
  intro he
  exact (not_le_of_gt hi) (paperCatalanFirstFixed_le f i he.symm)

end Posets
