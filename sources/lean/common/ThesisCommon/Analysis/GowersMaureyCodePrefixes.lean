import ThesisCommon.Analysis.GowersMaureyCoding
import Mathlib.Data.List.OfFn

/-! The actual injection used in special sequences decodes equal recursive
sizes into equal earlier functionals. All domain conditions are derived
from rationality and successive supports; no coding conclusion is assumed. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem initialSegment_codingDomain {k : ℕ} {g : Fin k → C00 𝕜}
    (hs : Successive g) (hr : ∀ i, RationalUnitSequence (g i)) (i : Fin k) :
    CodingDomain (initialSegment g i) := by
  constructor
  · intro x hx
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hx
    exact hr _
  · apply List.pairwise_ofFn.mpr
    intro s t hst
    apply hs
    exact hst

theorem SpecialSequence.initialSegment_codingDomain {D : ConstructionData 𝕜}
    {p : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (i : Fin k) :
    CodingDomain (initialSegment g i) :=
  GowersMaurey.initialSegment_codingDomain hg.1 hg.2.1 i

theorem ConstructionData.sigma_initialSegment_eq_iff (D : ConstructionData 𝕜)
    {k l : ℕ} {g : Fin k → C00 𝕜} {h : Fin l → C00 𝕜}
    (hg : Successive g) (hgr : ∀ i, RationalUnitSequence (g i))
    (hh : Successive h) (hhr : ∀ i, RationalUnitSequence (h i))
    (i : Fin k) (j : Fin l) :
    D.sigma (initialSegment g i) = D.sigma (initialSegment h j) ↔
      initialSegment g i = initialSegment h j := by
  constructor
  · exact D.sigma_injective (initialSegment_codingDomain hg hgr i)
      (initialSegment_codingDomain hh hhr j)
  · exact congrArg D.sigma

theorem ConstructionData.sigma_initialSegment_eq_imp_length (D : ConstructionData 𝕜)
    {k l : ℕ} {g : Fin k → C00 𝕜} {h : Fin l → C00 𝕜}
    (hg : Successive g) (hgr : ∀ i, RationalUnitSequence (g i))
    (hh : Successive h) (hhr : ∀ i, RationalUnitSequence (h i))
    (i : Fin k) (j : Fin l)
    (he : D.sigma (initialSegment g i) = D.sigma (initialSegment h j)) : i.val = j.val := by
  have hl := congrArg List.length ((D.sigma_initialSegment_eq_iff hg hgr hh hhr i j).mp he)
  simpa only [initialSegment, List.length_ofFn] using hl

theorem SpecialSequence.code_prefix_injective {D : ConstructionData 𝕜}
    {p : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) :
    Function.Injective (fun i => D.sigma (initialSegment g i)) := by
  intro i j he
  exact Fin.ext (D.sigma_initialSegment_eq_imp_length hg.1 hg.2.1 hg.1 hg.2.1 i j he)

theorem SpecialSequence.code_prefix_eq_imp_prefix {D : ConstructionData 𝕜}
    {p q : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g h : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (hh : SpecialSequence D q h) (i j : Fin k)
    (he : D.sigma (initialSegment g i) = D.sigma (initialSegment h j)) :
    i = j ∧ ∀ t : Fin k, t < i → g t = h t := by
  have hij : i = j := Fin.ext
    (D.sigma_initialSegment_eq_imp_length hg.1 hg.2.1 hh.1 hh.2.1 i j he)
  refine ⟨hij, ?_⟩
  subst j
  have hp := (D.sigma_initialSegment_eq_iff hg.1 hg.2.1 hh.1 hh.2.1 i i).mp he
  change List.ofFn (fun t : Fin i.val => g ⟨t.val, t.isLt.trans i.isLt⟩) =
    List.ofFn (fun t : Fin i.val => h ⟨t.val, t.isLt.trans i.isLt⟩) at hp
  have hf := List.ofFn_injective hp
  intro t ht
  have hv := congrFun hf ⟨t.val, ht⟩
  simpa using hv

theorem SpecialSequence.code_prefix_is_odd_size {D : ConstructionData 𝕜}
    {p : Seminorm 𝕜 (C00 𝕜)} {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : SpecialSequence D p g) (i : Fin k) :
    ∃ n, D.sigma (initialSegment g i) = D.j (2 * n + 1) :=
  D.sigma_even _ (hg.initialSegment_codingDomain i)

end ThesisCommon.GowersMaurey
