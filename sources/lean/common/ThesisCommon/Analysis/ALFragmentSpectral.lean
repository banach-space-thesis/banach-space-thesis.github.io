import ThesisCommon.Analysis.ALRenormSpectral
import ThesisCommon.Analysis.ALDedekindComplete

/-! Finite spectral approximations by genuine fragments of a positive
element. The approximation estimate uses only Dedekind completeness and
the solid norm; atomicity and a representation are not assumed. -/
noncomputable section
open Set
open scoped BigOperators ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
  [IsOrderedModule ℝ E] [HasSolidNorm E]

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
theorem positive_projection_fragment (P : E →L[ℝ] E) (hP : 0 ≤ P)
    (hP1 : P ≤ 1) (hid : P * P = P) {e : E} (he : 0 ≤ e) :
    IsPositiveFragment (P e) e := by
  have hr : 0 ≤ e - P e := sub_nonneg.mpr (hP1 e he)
  let z := P e ⊓ (e - P e)
  have hz : 0 ≤ z := le_inf (hP e he) hr
  have hid' : P (P e) = P e := congrArg (fun Q : E →L[ℝ] E => Q e) hid
  have hPz : P z = 0 := le_antisymm (by
    have h := positive_operator_monotone hP (show z ≤ e-P e from inf_le_right)
    simpa only [map_sub, hid', sub_self] using h) (hP z hz)
  have hQ : 0 ≤ (1 : E →L[ℝ] E) - P := sub_nonneg.mpr hP1
  have hz0 : z ≤ 0 := by
    have h := positive_operator_monotone hQ (show z ≤ P e from inf_le_left)
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      hPz, hid', sub_zero, sub_self] using h
  exact ⟨hP e he, hP1 e he, le_antisymm hz0 hz⟩

def positiveFragmentSpan (e : E) : Submodule ℝ E :=
  Submodule.span ℝ {a : E | IsPositiveFragment a e}

theorem positive_fragment_spectral_approximation {e x : E} (he : 0 ≤ e)
    (hx : 0 ≤ x) (hxe : x ≤ e) (n : ℕ) (hn : 0 < n) :
    ∃ v ∈ positiveFragmentSpan e, 0 ≤ x-v ∧ x-v ≤ (1/(n:ℝ)) • e := by
  classical
  let p (i : Fin n) : E →L[ℝ] E := principalBandProjection (x - ((i:ℝ)/n) • e)⁺
  have hp (i) : 0 ≤ p i := principalBandProjection_nonneg _
  have hp1 (i) : p i ≤ 1 := principalBandProjection_le_id _
  have hid (i) : p i * p i = p i := by
    ext y
    exact principalBandProjection_idempotent _ y
  have hcomm (i j) : Commute (p i) (p j) := by
    change p i * p j = p j * p i
    ext y
    exact principalBandProjection_commute _ _ y
  let Q (b : Fin n → Bool) := projectionAtom p b
  have hQ (b) : 0 ≤ Q b := projectionAtom_nonneg p hp hp1 b
  have hQ1 (b) : Q b ≤ 1 := projectionAtom_le_one p hp hp1 b
  have hQid (b) : Q b * Q b = Q b := projectionAtom_idempotent p hid hcomm b
  have hsum (y : E) : (∑ b, Q b y) = y := projectionAtom_sum_apply p y
  have ha (b : Fin n → Bool) : ∃ a : ℝ, 0 ≤ a ∧
      a • Q b e ≤ Q b x ∧ Q b x ≤ (a + 1/(n:ℝ)) • Q b e := by
    apply spectral_grid_interval (Q b e) (Q b x) (hQ b e he) (hQ b x hx)
      (positive_operator_monotone (hQ b) hxe) n hn
    intro i
    exact projectionAtom_cut_comparison p hp hp1 hid hcomm b i x e ((i:ℝ)/n)
      (principalBandProjection_cut_lower x e ((i:ℝ)/n))
      (principalBandProjection_cut_upper x e ((i:ℝ)/n))
  choose a ha0 hlo hhi using ha
  refine ⟨∑ b, a b • Q b e, ?_, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro b _
    apply Submodule.smul_mem
    exact Submodule.subset_span (positive_projection_fragment (Q b) (hQ b) (hQ1 b) (hQid b) he)
  · exact sub_nonneg.mpr (by
      have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hlo b)
      simpa only [hsum] using h)
  · apply sub_le_iff_le_add.mpr
    calc
      x = ∑ b, Q b x := (hsum x).symm
      _ ≤ ∑ b, (a b + 1/(n:ℝ)) • Q b e := Finset.sum_le_sum (fun b _ => hhi b)
      _ = (1/(n:ℝ)) • e + ∑ b, a b • Q b e := by
        simp only [add_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hsum]
        exact add_comm _ _

theorem positive_fragment_spectral_norm_approximation {e x : E} (he : 0 ≤ e)
    (hx : 0 ≤ x) (hxe : x ≤ e) (n : ℕ) (hn : 0 < n) :
    ∃ v ∈ positiveFragmentSpan e, ‖x-v‖ ≤ ‖e‖/(n:ℝ) := by
  obtain ⟨v, hv, h0, hle⟩ := positive_fragment_spectral_approximation he hx hxe n hn
  refine ⟨v, hv, (al_norm_mono h0 hle).trans_eq ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1/(n:ℝ))]
  ring

end ThesisCommon
