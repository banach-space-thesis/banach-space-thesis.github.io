import ThesisCommon.Analysis.ALRenormProjectionAtoms
import ThesisCommon.Analysis.ALRenormSpectralEstimate
import ThesisCommon.Analysis.ALRefinementPrincipalActions
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite spectral refinements prove the positive decomposition estimate
from a Banach-space isomorphism with an arbitrary-index real ell-one space. -/
noncomputable section
open Filter
open scoped BigOperators Topology ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
variable [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem projectionAtom_cut_comparison {n : ℕ} (p : Fin n → E →L[ℝ] E)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hid : ∀ i, p i * p i = p i) (hcomm : ∀ i j, Commute (p i) (p j))
    (ε : Fin n → Bool) (i : Fin n) (u x : E) (t : ℝ)
    (hlo : t • p i x ≤ p i u)
    (hhi : (1-p i) u ≤ t • (1-p i) x) :
    t • projectionAtom p ε x ≤ projectionAtom p ε u ∨
      projectionAtom p ε u ≤ t • projectionAtom p ε x := by
  have hpos := positive_operator_monotone (projectionAtom_nonneg p hp hp1 ε)
  have hsel := projectionAtom_selected_right p hid hcomm ε i
  cases he : ε i
  · right
    have hzero : ∀ y, projectionAtom p ε (p i y) = 0 := by
      intro y
      have h := congrArg (fun T : E →L[ℝ] E => T y) hsel
      simpa [he] using h
    have h := hpos hhi
    simpa only [map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      map_sub, hzero, sub_zero] using h
  · left
    have hone : ∀ y, projectionAtom p ε (p i y) = projectionAtom p ε y := by
      intro y
      have h := congrArg (fun T : E →L[ℝ] E => T y) hsel
      simpa [he] using h
    have h := hpos hlo
    simpa only [map_smul, hone] using h

theorem positive_decomposition_grid_bound_of_equiv_ellOne [Fintype J]
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) (A C : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (u : J → E) (hu : ∀ j, 0 ≤ u j) (n : ℕ) (hn : 0 < n) :
    (∑ j, ‖u j‖) ≤ (1 + (Fintype.card J : ℝ) * (1/n)) *
      (128*A*C)^2 * ‖∑ j, u j‖ := by
  classical
  let x := ∑ j, u j
  have hx : 0 ≤ x := Finset.sum_nonneg fun j _ => hu j
  let e : Fin (Fintype.card (J × Fin n)) ≃ J × Fin n := (Fintype.equivFin _).symm
  let p (i : Fin (Fintype.card (J × Fin n))) : E →L[ℝ] E :=
    principalBandProjection (u (e i).1 - (((e i).2 : ℝ)/n) • x)⁺
  have hp (i) : 0 ≤ p i := principalBandProjection_nonneg _
  have hp1 (i) : p i ≤ 1 := principalBandProjection_le_id _
  have hid (i) : p i * p i = p i := by
    ext y
    exact principalBandProjection_idempotent _ y
  have hcomm (i j) : Commute (p i) (p j) := by
    change p i * p j = p j * p i
    ext y
    exact principalBandProjection_commute _ _ y
  let Q (ε : Fin (Fintype.card (J × Fin n)) → Bool) := projectionAtom p ε
  have hQ (ε) : 0 ≤ Q ε := projectionAtom_nonneg p hp hp1 ε
  have hQsum (y : E) : (∑ ε, Q ε y) = y := projectionAtom_sum_apply p y
  have hQnorm : (∑ ε, ‖Q ε x‖) ≤ (128*A*C)^2 * ‖x‖ := by
    apply positive_orthogonal_projection_sum_norm_le d A C hA hC hd hdinv Q hQ
    · intro ε
      exact projectionAtom_le_one p hp hp1 ε
    · intro ε y
      exact congrArg (fun T : E →L[ℝ] E => T y) (projectionAtom_idempotent p hid hcomm ε)
    · intro ε η hne y
      exact congrArg (fun T : E →L[ℝ] E => T y) (projectionAtom_orthogonal p hid hcomm ε η hne)
  have happrox (j : J) (ε : Fin (Fintype.card (J × Fin n)) → Bool) :
      ∃ a : ℝ, 0 ≤ a ∧ a • Q ε x ≤ Q ε (u j) ∧
        Q ε (u j) ≤ (a+1/n) • Q ε x := by
    apply spectral_grid_interval (Q ε x) (Q ε (u j)) (hQ ε x hx) (hQ ε (u j) (hu j))
      (positive_operator_monotone (hQ ε) (Finset.single_le_sum (fun k _ => hu k)
        (Finset.mem_univ j))) n hn
    intro k
    have hlo : ((k : ℝ)/n) • p (e.symm (j,k)) x ≤ p (e.symm (j,k)) (u j) := by
      simpa only [p, Equiv.apply_symm_apply] using
        principalBandProjection_cut_lower (u j) x ((k : ℝ)/n)
    have hhi : (1-p (e.symm (j,k))) (u j) ≤
        ((k : ℝ)/n) • (1-p (e.symm (j,k))) x := by
      simpa only [p, Equiv.apply_symm_apply] using
        principalBandProjection_cut_upper (u j) x ((k : ℝ)/n)
    exact projectionAtom_cut_comparison p hp hp1 hid hcomm ε (e.symm (j,k))
      (u j) x ((k : ℝ)/n) hlo hhi
  choose a ha hlo hhi using happrox
  exact positive_sum_bound_of_spectral_cells u hu Q hQ hQsum ((128*A*C)^2) (1/n)
    (sq_nonneg _) (by positivity) hQnorm a ha hlo hhi

/-- Every finite positive decomposition obeys a uniform lower estimate.
The proof constructs commuting principal-band cuts, refines them into
orthogonal cells, and sends their scalar approximation mesh to zero. -/
theorem positive_decomposition_bound_of_equiv_ellOne [Fintype J]
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) (A C : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (u : J → E) (hu : ∀ j, 0 ≤ u j) :
    (∑ j, ‖u j‖) ≤ (128*A*C)^2 * ‖∑ j, u j‖ := by
  have hlim : Tendsto (fun m : ℕ =>
      (1 + (Fintype.card J : ℝ) * (1/((m:ℝ)+1))) * (128*A*C)^2 * ‖∑ j, u j‖)
      atTop (𝓝 ((128*A*C)^2 * ‖∑ j, u j‖)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using ((hone.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Fintype.card J : ℝ))).mul_const
      ((128*A*C)^2)).mul_const ‖∑ j, u j‖
  apply ge_of_tendsto' hlim
  intro m
  simpa only [Nat.cast_add, Nat.cast_one] using
    positive_decomposition_grid_bound_of_equiv_ellOne d A C hA hC hd hdinv u hu (m+1)
      (Nat.succ_pos m)

end ThesisCommon
