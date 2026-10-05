import Sigma.ProofTargets
import ThesisCommon.Analysis.NormingEmbedding
import ThesisCommon.Analysis.NormingTransport
import Sigma.CountableNorming

/-! The norming-coordinate implication in Proposition 3.4 needs no dual hypothesis. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
open scoped BoundedContinuousFunction

local instance boundedSubmoduleGroup (S : Submodule ℝ (ℕ →ᵇ ℝ)) : NormedAddCommGroup S :=
  inferInstance
local instance boundedSubmoduleSpace (S : Submodule ℝ (ℕ →ᵇ ℝ)) : NormedSpace ℝ S :=
  inferInstance

theorem sublattice_of_not_desiredProperty (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (h : ¬ DesiredProperty E) :
    IsomorphicToSublatticeEllInfinity E := by
  obtain ⟨e, ⟨c, he⟩, hmod⟩ := (not_desiredProperty_iff (E := E)).mp h
  let T := normingCoordinates e he.2.2.1
  let S := LinearMap.range T
  have hclosed : IsClosed (S : Set (ℕ →ᵇ ℝ)) :=
    (normingCoordinates_antilipschitz he).isClosed_range T.uniformContinuous
  refine ⟨S, hclosed, ?_, ⟨normingCoordinatesEquiv he⟩⟩
  rintro f ⟨x, rfl⟩ g ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hmod (x - y)
  constructor
  · refine ⟨(1 / 2 : ℝ) • (x + y + z), ?_⟩
    ext n
    change e n ((1 / 2 : ℝ) • (x + y + z)) = max (e n x) (e n y)
    rw [map_smul, map_add, map_add, hz n, map_sub]
    change (1 / 2 : ℝ) * (e n x + e n y + |e n x - e n y|) = _
    by_cases hxy : e n x ≤ e n y
    · rw [max_eq_right hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    · have hyx := lt_of_not_ge hxy
      rw [max_eq_left hyx.le, abs_of_nonneg (sub_nonneg.mpr hyx.le)]
      ring
  · refine ⟨(1 / 2 : ℝ) • (x + y - z), ?_⟩
    ext n
    change e n ((1 / 2 : ℝ) • (x + y - z)) = min (e n x) (e n y)
    rw [map_smul, map_sub, map_add, hz n, map_sub]
    change (1 / 2 : ℝ) * (e n x + e n y - |e n x - e n y|) = _
    by_cases hxy : e n x ≤ e n y
    · rw [min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    · have hyx := lt_of_not_ge hxy
      rw [min_eq_right hyx.le, abs_of_nonneg (sub_nonneg.mpr hyx.le)]
      ring

theorem not_desiredProperty_of_sublattice (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (h : IsomorphicToSublatticeEllInfinity E) : ¬ DesiredProperty E := by
  obtain ⟨S, _, hlat, ⟨T⟩⟩ := h
  apply not_desiredProperty_of_equiv (E := E) (F := S) T
  apply (not_desiredProperty_iff (E := S)).mpr
  refine ⟨fun n => submoduleEvaluation S n,
    ⟨1, submoduleEvaluation_oneNorming S id Function.surjective_id⟩, ?_⟩
  intro f
  refine ⟨⟨f.val ⊔ -f.val, (hlat f.val f.property (-f.val) (S.neg_mem f.property)).1⟩, ?_⟩
  intro n
  change max (f.val n) (-f.val n) = |f.val n|
  by_cases hn : 0 ≤ f.val n
  · rw [abs_of_nonneg hn, max_eq_left (by linarith)]
  · have hn' := le_of_not_ge hn
    rw [abs_of_nonpos hn', max_eq_right (by linarith)]

/-- The second equivalence of Proposition 3.4 holds for every Banach space. -/
theorem sublattice_iff_not_desiredProperty (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] :
    IsomorphicToSublatticeEllInfinity E ↔ ¬ DesiredProperty E :=
  ⟨not_desiredProperty_of_sublattice E, sublattice_of_not_desiredProperty E⟩

end SigmaNonprimarity
