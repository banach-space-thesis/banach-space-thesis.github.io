import ThesisCommon.Analysis.LpHaarSequentialGeometry

/-! Two-sided selection for normalized block matrix entries. The functionals
and vectors in the finite history are rescaled using the prescribed parent
norm before selection, so small raw entries are never mistaken for small
normalized entries. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def lpHaarNormalizedBlockEntry (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (S R : LpHaarFiniteSplit) : 𝕜 :=
  (‖S.vector 𝕜 p‖ : 𝕜) * (‖R.vector 𝕜 p‖ : 𝕜)⁻¹ * S.reader 𝕜 p (T (R.vector 𝕜 p))

include hp in
theorem lpHaar_infinite_normalized_selection
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) :
    ∃ F : LpHaarSequentialSplits, ∀ j (i : Fin j),
      ‖lpHaarNormalizedBlockEntry 𝕜 p T (F.node i.val) (F.node j)‖ < ε j ∧
      ‖lpHaarNormalizedBlockEntry 𝕜 p T (F.node j) (F.node i.val)‖ < ε j := by
  apply exists_haar_split_history
    (fun j _ h S => ∀ i : Fin j,
      ‖lpHaarNormalizedBlockEntry 𝕜 p T (h i) S‖ < ε j ∧
      ‖lpHaarNormalizedBlockEntry 𝕜 p T S (h i)‖ < ε j)
  intro j P h
  let N : ℝ := (volume.restrict (Icc (0 : ℝ) 1)).real P.set ^ (1 / p.val.toReal)
  let φ (i : Fin j) := ((‖(h i).vector 𝕜 p‖ : 𝕜) * (N : 𝕜)⁻¹) •
    (((h i).reader 𝕜 p).comp T)
  let f (i : Fin j) := ((N : 𝕜) * (‖(h i).vector 𝕜 p‖ : 𝕜)⁻¹) •
    T ((h i).vector 𝕜 p)
  obtain ⟨S, hlevel, hparent, hf, hb⟩ := lpHaarFiniteParent_select 𝕜 p hp φ f P j (hε j)
  have hnorm : ‖S.vector 𝕜 p‖ = N := by
    rw [LpHaarFiniteSplit.vector, lpHaarSignedBlock_norm 𝕜 p hp]
    change (volume.restrict (Icc (0 : ℝ) 1)).real S.parent.set ^ (1 / p.val.toReal) = N
    rw [hparent]
  refine ⟨S, hlevel, hparent, fun i => ⟨?_, ?_⟩⟩
  · simpa only [φ, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, lpHaarNormalizedBlockEntry, hnorm] using hf i
  · simpa only [f, map_smul, smul_eq_mul, lpHaarNormalizedBlockEntry, hnorm] using hb i

end ThesisCommon
