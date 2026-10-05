import ThesisCommon.Analysis.SigmaComplexLatticeStructure
import ThesisCommon.Analysis.SigmaComplexLatticeProduct
import ThesisCommon.Analysis.AtomicDualOrder
import Sigma.ComplexDesiredProperty

/-! Countable real lattice homomorphisms complexify to a complex norming
sequence that realizes the modulus. The final theorem reduces only the
existence of the ordered real dual model to the independent representation
theorem. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
open scoped ThesisCommon.SigmaComplexLatticeProduct

theorem complexifyFunctional_isNorming (F : ComplexBanachLattice)
    (e : ℕ → F.RealPart →L[ℝ] ℝ) (he : IsNorming e) :
    IsComplexNorming (fun n => F.complexifyFunctional (e n)) := by
  obtain ⟨c,hc⟩ := he
  have hunit (n : ℕ) : ‖F.complexifyFunctional (e n)‖ ≤ 1 :=
    (F.complexifyFunctional_norm_le _).trans (hc.2.2.1 n)
  refine ⟨c/2,by linarith [hc.1],by linarith [hc.2.1],hunit,?_⟩
  intro z
  let S : ℝ := ⨆ n, ‖F.complexifyFunctional (e n) z‖
  have hb := complex_evaluations_bddAbove (fun n => F.complexifyFunctional (e n)) hunit z
  have hr : c*‖F.re z‖ ≤ S := by
    apply (hc.2.2.2 (F.re z)).trans
    apply ciSup_le
    intro n
    exact (show |e n (F.re z)| ≤ ‖F.complexifyFunctional (e n) z‖ from by
      rw [F.complexifyFunctional_apply]
      exact Complex.abs_re_le_norm (⟨e n (F.re z),e n (F.im z)⟩ : ℂ)).trans (le_ciSup hb n)
  have hi : c*‖F.im z‖ ≤ S := by
    apply (hc.2.2.2 (F.im z)).trans
    apply ciSup_le
    intro n
    exact (show |e n (F.im z)| ≤ ‖F.complexifyFunctional (e n) z‖ from by
      rw [F.complexifyFunctional_apply]
      exact Complex.abs_im_le_norm (⟨e n (F.re z),e n (F.im z)⟩ : ℂ)).trans (le_ciSup hb n)
  have hn := mul_le_mul_of_nonneg_left (F.norm_le_re_add_im z) hc.1.le
  change c/2*‖z‖ ≤ S
  nlinarith

theorem complex_not_desiredProperty_of_real_norming_latticeHoms (F : ComplexBanachLattice)
    (e : ℕ → F.RealPart →L[ℝ] ℝ) (he : IsNorming e)
    (habs : ∀ n x, e n |x| = |e n x|) : ¬ ComplexDesiredProperty F := by
  apply (not_complexDesiredProperty_iff (E := F)).mpr
  refine ⟨fun n => F.complexifyFunctional (e n),complexifyFunctional_isNorming F e he,?_⟩
  intro z
  exact ⟨F.ofReal (F.modulus z),fun n => F.complexifyFunctional_modulus (e n) (habs n) z⟩

theorem realNorming_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℕ → (E × E) →L[ℝ] ℝ) (he : IsNorming e) :
    IsNorming (fun n => (e n).comp (ContinuousLinearMap.inl ℝ E E)) := by
  obtain ⟨c,hc⟩ := he
  refine ⟨c,hc.1,hc.2.1,?_,?_⟩
  · intro n
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    have h := (e n).le_opNorm (x,0)
    have hn : ‖(x,(0 : E))‖ = ‖x‖ := by simp
    rw [hn] at h
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,one_mul] using
      h.trans (by simpa using mul_le_mul_of_nonneg_right (hc.2.2.1 n) (norm_nonneg x))
  · intro x
    simpa using hc.2.2.2 (x,0)

/-- The product lattice is used only as a real Banach lattice; the complex
modulus remains the intrinsic modulus on F, rather than the coordinatewise
real product modulus. -/
theorem complex_not_desiredProperty_of_ordered_real_product (F : ComplexBanachLattice)
    {I : Type*}
    (d : ((F.RealPart × F.RealPart) →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (horder : ∀ φ : (F.RealPart × F.RealPart) →L[ℝ] ℝ, 0 ≤ φ ↔ ∀ i, 0 ≤ d φ i)
    (he : ∃ e : ℕ → (F.RealPart × F.RealPart) →L[ℝ] ℝ, IsNorming e) :
    ¬ ComplexDesiredProperty F := by
  obtain ⟨e,he⟩ := he
  obtain ⟨q,hq⟩ := exists_norming_dual_atoms d e he
  let a : ℕ → (F.RealPart × F.RealPart) →L[ℝ] ℝ := fun n => normalizedDualAtom d (q n)
  apply complex_not_desiredProperty_of_real_norming_latticeHoms F
    (fun n => (a n).comp (ContinuousLinearMap.inl ℝ _ _)) (realNorming_fst a hq)
  intro n x
  have h := normalizedDualAtom_abs d
    (fun i z => (dualAtom_isPositiveFunctionalAtom d horder i).map_abs z) (q n) (x,0)
  simpa only [a,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
    complexLatticeProduct_abs,abs_zero] using h

end SigmaNonprimarity

