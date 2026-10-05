import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Encodable.Basic

/-! An explicit independent family on a countable set gives at least
`2^continuum` ultrafilters on the natural numbers. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Filter
namespace Posets

private def separatingCoordinate (A B : Set ℕ) : ℕ :=
  if h : A = B then 0 else Classical.choose (show ∃ n, ¬ (n ∈ A ↔ n ∈ B) from
    not_forall.mp (fun hh => h (Set.ext hh)))

private theorem separatingCoordinate_spec {A B : Set ℕ} (h : A ≠ B) :
    ¬ (separatingCoordinate A B ∈ A ↔ separatingCoordinate A B ∈ B) := by
  classical
  simp only [separatingCoordinate, dif_neg h]
  exact Classical.choose_spec (not_forall.mp (fun hh => h (Set.ext hh)))

/-- Finitely many distinct subsets can be distinguished on finitely many coordinates. -/
theorem exists_finset_separating_sets (F : Finset (Set ℕ)) :
    ∃ s : Finset ℕ, Set.InjOn (fun A : Set ℕ => s.filter (fun n => n ∈ A)) (↑F) := by
  classical
  let s := (F ×ˢ F).image (fun p => separatingCoordinate p.1 p.2)
  refine ⟨s, ?_⟩
  intro A hA B hB heq
  dsimp only at heq
  by_contra hne
  have hn : separatingCoordinate A B ∈ s :=
    Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, rfl⟩
  apply separatingCoordinate_spec hne
  simpa only [Finset.mem_filter, hn, true_and] using
    (show separatingCoordinate A B ∈ s.filter (fun n => n ∈ A) ↔
      separatingCoordinate A B ∈ s.filter (fun n => n ∈ B) from by rw [heq])

/-- A countable set on which continuum many independent subsets are represented. -/
abbrev IndependentFamilyDomain := Finset ℕ × Finset (Finset ℕ)

def independentCoordinate (A : Set ℕ) : Set IndependentFamilyDomain :=
  {x | x.1.filter (fun n => n ∈ A) ∈ x.2}

/-- Every finite pattern in the family can be realised. -/
theorem independentCoordinate_finite_pattern (F : Finset (Set ℕ)) (Y : Set (Set ℕ)) :
    ∃ x : IndependentFamilyDomain, ∀ A ∈ F, (x ∈ independentCoordinate A ↔ A ∈ Y) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_separating_sets F
  refine ⟨(s, (F.filter (fun A => A ∈ Y)).image (fun A => s.filter (fun n => n ∈ A))), ?_⟩
  intro A hA
  change s.filter (fun n => n ∈ A) ∈
    (F.filter (fun A => A ∈ Y)).image (fun A => s.filter (fun n => n ∈ A)) ↔ A ∈ Y
  constructor
  · intro h
    obtain ⟨B, hB, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hBF, hBY⟩ := Finset.mem_filter.mp hB
    exact hs hBF hA heq ▸ hBY
  · intro hAY
    exact Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, hAY⟩, rfl⟩

private def patternGenerator (Y : Set (Set ℕ)) (A : Set ℕ) : Set IndependentFamilyDomain :=
  {x | x ∈ independentCoordinate A ↔ A ∈ Y}

theorem exists_ultrafilter_realizing_pattern (Y : Set (Set ℕ)) :
    ∃ U : Ultrafilter IndependentFamilyDomain,
      ∀ A : Set ℕ, independentCoordinate A ∈ U ↔ A ∈ Y := by
  classical
  obtain ⟨U, hU⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty
    (Set.range (patternGenerator Y)) (by
      intro T hT
      have hex (t : T) : ∃ A, patternGenerator Y A = t.val := hT t.property
      let a (t : T) := Classical.choose (hex t)
      obtain ⟨x, hx⟩ := independentCoordinate_finite_pattern (Finset.univ.image a) Y
      refine ⟨x, ?_⟩
      intro t ht
      let t' : T := ⟨t, ht⟩
      have hh := hx (a t') (Finset.mem_image.mpr ⟨t', Finset.mem_univ _, rfl⟩)
      have ha := Classical.choose_spec (hex t')
      change patternGenerator Y (a t') = t at ha
      change x ∈ t
      rw [← ha]
      exact hh)
  refine ⟨U, fun A => ?_⟩
  have hg : patternGenerator Y A ∈ U := hU (Set.mem_range_self A)
  by_cases hA : A ∈ Y
  · have he : patternGenerator Y A = independentCoordinate A := by
      ext x
      simp [patternGenerator, hA]
    simp only [he] at hg
    exact iff_of_true hg hA
  · have he : patternGenerator Y A = (independentCoordinate A)ᶜ := by
      ext x
      simp [patternGenerator, hA]
    rw [he, Ultrafilter.compl_mem_iff_notMem] at hg
    exact iff_of_false hg hA

/-- Distinct subfamilies give distinct ultrafilters. -/
def ultrafilterPatternEmbedding : Set (Set ℕ) ↪ Ultrafilter IndependentFamilyDomain where
  toFun Y := Classical.choose (exists_ultrafilter_realizing_pattern Y)
  inj' := by
    intro Y Z h
    change Classical.choose (exists_ultrafilter_realizing_pattern Y) =
      Classical.choose (exists_ultrafilter_realizing_pattern Z) at h
    ext A
    rw [← Classical.choose_spec (exists_ultrafilter_realizing_pattern Y) A,
      ← Classical.choose_spec (exists_ultrafilter_realizing_pattern Z) A, h]

/-- There are at least `2^continuum` ultrafilters on `ℕ`, with no cardinal
arithmetic or continuum hypothesis used in the construction. -/
def manyUltrafiltersEmbedding : Set (Set ℕ) ↪ Ultrafilter ℕ := by
  let e := Classical.choose (exists_injective_nat IndependentFamilyDomain)
  have he := Classical.choose_spec (exists_injective_nat IndependentFamilyDomain)
  exact ultrafilterPatternEmbedding.trans
    ⟨Ultrafilter.map e, fun U V h => Ultrafilter.coe_injective
      (Filter.map_injective he (congrArg Ultrafilter.toFilter h))⟩

end Posets
