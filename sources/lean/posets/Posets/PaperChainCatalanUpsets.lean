import Posets.PaperChainCatalanMaps
import Posets.IdealCounts

/-! Interval upsets of a d-point chain correspond to monotone extensive
maps on d+1 points, by taking the first admitted right endpoint in each row.
The extra point is the sentinel for an empty row. -/
noncomputable section
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets

def paperChainCandidates {d : ℕ} (W : IntervalUpsets (Fin d)) (i : Fin (d + 1)) :
    Finset (Fin (d + 1)) := Finset.univ.filter (fun j => j.val = d ∨
      ∃ (hi : i.val < d) (hj : j.val < d) (hij : i.val ≤ j.val),
        (⟨(⟨i.val, hi⟩, ⟨j.val, hj⟩), hij⟩ : {st : Fin d × Fin d // st.1 ≤ st.2}) ∈ W.val)

theorem paperChainCandidates_nonempty {d : ℕ} (W : IntervalUpsets (Fin d))
    (i : Fin (d + 1)) : (paperChainCandidates W i).Nonempty :=
  ⟨Fin.last d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩⟩

def paperChainBoundary {d : ℕ} (W : IntervalUpsets (Fin d)) (i : Fin (d + 1)) : Fin (d + 1) :=
  (paperChainCandidates W i).min' (paperChainCandidates_nonempty W i)

theorem paperChainBoundary_mem {d : ℕ} (W : IntervalUpsets (Fin d)) (i : Fin (d + 1)) :
    paperChainBoundary W i ∈ paperChainCandidates W i := Finset.min'_mem _ _

theorem paperChainBoundary_le {d : ℕ} (W : IntervalUpsets (Fin d)) (i j : Fin (d + 1))
    (hj : j ∈ paperChainCandidates W i) : paperChainBoundary W i ≤ j :=
  Finset.min'_le _ _ hj

theorem paperChainBoundary_extensive {d : ℕ} (W : IntervalUpsets (Fin d)) (i : Fin (d + 1)) :
    i ≤ paperChainBoundary W i := by
  obtain h | ⟨_, _, h, _⟩ := (Finset.mem_filter.mp (paperChainBoundary_mem W i)).2
  · change i.val ≤ (paperChainBoundary W i).val
    omega
  · exact h

theorem paperChainBoundary_monotone {d : ℕ} (W : IntervalUpsets (Fin d)) :
    Monotone (paperChainBoundary W) := by
  intro i k hik
  apply paperChainBoundary_le
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  obtain h | ⟨hk, hj, hkj, hw⟩ := (Finset.mem_filter.mp (paperChainBoundary_mem W k)).2
  · exact Or.inl h
  · have hik' : i.val ≤ k.val := hik
    have hi : i.val < d := by omega
    have hij : i.val ≤ (paperChainBoundary W k).val := by omega
    exact Or.inr ⟨hi, hj, hij, W.property _ hw _ hik le_rfl⟩

def paperChainEncode {d : ℕ} (W : IntervalUpsets (Fin d)) : PaperCatalanMap (d + 1) :=
  ⟨paperChainBoundary W, paperChainBoundary_monotone W, paperChainBoundary_extensive W⟩

def paperChainDecode {d : ℕ} (f : PaperCatalanMap (d + 1)) : IntervalUpsets (Fin d) :=
  ⟨{i | f.val i.val.1.castSucc ≤ i.val.2.castSucc}, by
    intro i hi j hji hij
    exact (f.property.1 hji).trans (hi.trans hij)⟩

theorem paperChainDecode_encode {d : ℕ} (W : IntervalUpsets (Fin d)) :
    paperChainDecode (paperChainEncode W) = W := by
  apply Subtype.ext
  ext i
  change paperChainBoundary W i.val.1.castSucc ≤ i.val.2.castSucc ↔ i ∈ W.val
  constructor
  · intro h
    obtain he | ⟨ha, hb, hab, hw⟩ :=
      (Finset.mem_filter.mp (paperChainBoundary_mem W i.val.1.castSucc)).2
    · have h' : (paperChainBoundary W i.val.1.castSucc).val ≤ i.val.2.val := h
      omega
    · exact W.property _ hw i le_rfl h
  · intro hi
    apply paperChainBoundary_le
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
    exact ⟨i.val.1.isLt, i.val.2.isLt, i.property, hi⟩

theorem paperChainEncode_decode {d : ℕ} (f : PaperCatalanMap (d + 1)) :
    paperChainEncode (paperChainDecode f) = f := by
  apply Subtype.ext
  funext i
  apply le_antisymm
  · apply paperChainBoundary_le
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_cases he : (f.val i).val = d
    · exact Or.inl he
    · have hj : (f.val i).val < d := by have := (f.val i).isLt; omega
      have hle : i.val ≤ (f.val i).val := f.property.2 i
      have hi : i.val < d := by omega
      refine Or.inr ⟨hi, hj, hle, ?_⟩
      change f.val ⟨i.val, by omega⟩ ≤ ⟨(f.val i).val, by omega⟩
      exact le_rfl
  · change f.val i ≤ paperChainBoundary (paperChainDecode f) i
    obtain he | ⟨hi, hj, hij, hw⟩ :=
      (Finset.mem_filter.mp (paperChainBoundary_mem (paperChainDecode f) i)).2
    · change (f.val i).val ≤ (paperChainBoundary (paperChainDecode f) i).val
      have := (f.val i).isLt
      omega
    · exact hw

def paperChainUpsetsCatalanEquiv (d : ℕ) : IntervalUpsets (Fin d) ≃ PaperCatalanMap (d + 1) where
  toFun := paperChainEncode
  invFun := paperChainDecode
  left_inv := paperChainDecode_encode
  right_inv := paperChainEncode_decode

end Posets
