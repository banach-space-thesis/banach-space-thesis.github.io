import ThesisCommon.Analysis.InfinityQuotientEvaluation
import ThesisCommon.Analysis.InfiniteSubsetStabilization
import Mathlib.Topology.Compactification.StoneCech

/-! The actual Stone topology on free ultrafilters on the natural numbers.
This is the ultrafilter model of the Stone--Čech remainder. Its clopen
neighbourhoods are represented by infinite subsets modulo finite sets. -/
noncomputable section
namespace ThesisCommon
open Set Filter Topology

namespace FreeNatUltrafilter

instance : TopologicalSpace FreeNatUltrafilter :=
  inferInstanceAs (TopologicalSpace {U : Ultrafilter ℕ // (U : Filter ℕ) ≤ cofinite})

instance : T2Space FreeNatUltrafilter :=
  inferInstanceAs (T2Space {U : Ultrafilter ℕ // (U : Filter ℕ) ≤ cofinite})

theorem isClosed_setOf_free :
    IsClosed {U : Ultrafilter ℕ | (U : Filter ℕ) ≤ cofinite} := by
  have he : {U : Ultrafilter ℕ | (U : Filter ℕ) ≤ cofinite} =
      ⋂ n : ℕ, {U : Ultrafilter ℕ | {n}ᶜ ∈ U} := by
    ext U
    simp only [mem_setOf_eq, mem_iInter, Filter.le_cofinite_iff_compl_singleton_mem]
    rfl
  rw [he]
  exact isClosed_iInter (fun n => ultrafilter_isClosed_basic {n}ᶜ)

instance : CompactSpace FreeNatUltrafilter :=
  isCompact_iff_compactSpace.mp isClosed_setOf_free.isCompact

instance : Nonempty FreeNatUltrafilter := by
  obtain ⟨U, _⟩ := exists_mem (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  exact ⟨U⟩

def basic (A : Set ℕ) : Set FreeNatUltrafilter := {U | A ∈ U}

theorem isClopen_basic (A : Set ℕ) : IsClopen (basic A) :=
  ⟨(ultrafilter_isClosed_basic A).preimage continuous_subtype_val,
    (ultrafilter_isOpen_basic A).preimage continuous_subtype_val⟩

@[simp] theorem basic_univ : basic Set.univ = Set.univ := by
  ext U
  simp only [basic, mem_setOf_eq, mem_univ, iff_true]
  exact Filter.univ_mem

@[simp] theorem basic_empty : basic ∅ = ∅ := by
  ext U
  simp only [basic, mem_setOf_eq, mem_empty_iff_false, iff_false]
  exact Filter.empty_notMem (U.val : Filter ℕ)

@[simp] theorem basic_inter (A B : Set ℕ) : basic (A ∩ B) = basic A ∩ basic B := by
  ext U
  exact Filter.inter_mem_iff

@[simp] theorem basic_union (A B : Set ℕ) : basic (A ∪ B) = basic A ∪ basic B := by
  ext U
  exact U.val.union_mem_iff

@[simp] theorem basic_compl (A : Set ℕ) : basic Aᶜ = (basic A)ᶜ := by
  ext U
  exact U.val.compl_mem_iff_notMem

theorem basic_nonempty_iff (A : Set ℕ) : (basic A).Nonempty ↔ A.Infinite :=
  ⟨fun ⟨U, hU⟩ => U.infinite_of_mem hU, exists_mem⟩

theorem basic_mono_mod_finite {A B : Set ℕ} (h : (A \ B).Finite) : basic A ⊆ basic B :=
  fun U hU => Filter.mem_of_superset
    (Filter.inter_mem hU (U.property h.compl_mem_cofinite)) (by
      intro n hn
      by_contra hB
      exact hn.2 ⟨hn.1, hB⟩)

theorem exists_basic_subset {s : Set FreeNatUltrafilter} (hs : IsOpen s)
    {U : FreeNatUltrafilter} (hU : U ∈ s) :
    ∃ A : Set ℕ, A ∈ U ∧ basic A ⊆ s := by
  have hb := ultrafilterBasis_is_basis.induced (fun U : FreeNatUltrafilter => U.val)
  obtain ⟨W, ⟨V, ⟨A, rfl⟩, rfl⟩, hW, hWs⟩ := hb.mem_nhds_iff.mp (hs.mem_nhds hU)
  exact ⟨A, hW, hWs⟩

/-- Countably many nested nonempty basic clopens have a nonempty basic
clopen lower bound; the underlying subset is an infinite pseudointersection. -/
theorem exists_basic_lower_bound (A : ℕ → Set ℕ)
    (hA : ∀ n, (A n).Infinite) (hanti : Antitone A) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A 0 ∧ ∀ n, basic B ⊆ basic (A n) := by
  obtain ⟨B, hB, hBA, hfin⟩ := infinite_nested_pseudointersection A hA hanti
  exact ⟨B, hB, hBA, fun n => basic_mono_mod_finite (hfin n)⟩

end FreeNatUltrafilter
end ThesisCommon
