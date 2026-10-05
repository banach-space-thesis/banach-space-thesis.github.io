import ThesisCommon.Analysis.ALFragmentSpectral

/-! A principal band in a complete real AL-lattice is the norm closure of
the linear span of the fragments of its generator. This is the density
statement required for a non-atomic finite-measure representation. -/
noncomputable section
open Set Filter Topology
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
  [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem isClosed_principalBand (e : E) : IsClosed (principalBand e : Set E) := by
  have heq : (principalBand e : Set E) = {x | principalBandProjection e x = x} := by
    ext x
    constructor
    · exact (principalBand_orderClosed e).bandProjection_eq_self
    · intro h
      rw [← h]
      exact (principalBand_orderClosed e).bandProjection_mem x
  rw [heq]
  exact isClosed_eq (principalBandProjection e).continuous continuous_id

theorem positiveFragmentSpan_le_principalBand (e : E) :
    positiveFragmentSpan e ≤ principalBand e := by
  apply Submodule.span_le.mpr
  intro a ha
  exact (principalBand_orderClosed e).nonneg_le_mem (self_mem_principalBand e) ha.1 ha.2.1

theorem mem_fragmentSpan_closure_of_nonneg_le {e x : E} (he : 0 ≤ e)
    (hx : 0 ≤ x) (hxe : x ≤ e) : x ∈ (positiveFragmentSpan e).topologicalClosure := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (‖e‖/ε)
  have hnR : (0 : ℝ) < n := (div_nonneg (norm_nonneg e) hε.le).trans_lt hn
  have hnN : 0 < n := by exact_mod_cast hnR
  obtain ⟨v, hv, herr⟩ := positive_fragment_spectral_norm_approximation he hx hxe n hnN
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm]
  apply herr.trans_lt
  apply (div_lt_iff₀ hnR).mpr
  have h := (div_lt_iff₀ hε).mp hn
  nlinarith

theorem mem_fragmentSpan_closure_of_nonneg_le_nsmul {e x : E} (he : 0 ≤ e)
    (hx : 0 ≤ x) (n : ℕ) (hxe : x ≤ n • e) :
    x ∈ (positiveFragmentSpan e).topologicalClosure := by
  cases n with
  | zero =>
    have hx0 : x = 0 := le_antisymm (by simpa using hxe) hx
    rw [hx0]
    exact Submodule.zero_mem _
  | succ n =>
    have hn : (0 : ℝ) < (n+1:ℕ) := by positivity
    have hscaled : ((n+1:ℕ):ℝ)⁻¹ • x ≤ e := by
      have h := smul_le_smul_of_nonneg_left hxe (inv_nonneg.mpr hn.le)
      simpa only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn.ne', one_smul] using h
    have hmem := mem_fragmentSpan_closure_of_nonneg_le he
      (smul_nonneg (inv_nonneg.mpr hn.le) hx) hscaled
    have h := (positiveFragmentSpan e).topologicalClosure.smul_mem ((n+1:ℕ):ℝ) hmem
    simpa only [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] using h

variable [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
include hAL

theorem mem_fragmentSpan_closure_of_principalBand_nonneg {e x : E} (he : 0 ≤ e)
    (hx : 0 ≤ x) (hxB : x ∈ principalBand e) :
    x ∈ (positiveFragmentSpan e).topologicalClosure := by
  let s := principalPositiveBelow e x
  have hs : s.Nonempty := ⟨0, le_rfl, hx, 0, by simp⟩
  have hpos : ∀ y ∈ s, 0 ≤ y := fun _ hy => hy.1
  have hdir : DirectedOn (· ≤ ·) s := by
    intro u hu v hv
    obtain ⟨hu0, hux, n, hun⟩ := hu
    obtain ⟨hv0, hvx, m, hvm⟩ := hv
    refine ⟨u ⊔ v, ⟨hu0.trans le_sup_left, sup_le hux hvx, n+m, ?_⟩,
      le_sup_left, le_sup_right⟩
    rw [add_nsmul]
    exact sup_le (hun.trans (le_add_of_nonneg_right (nsmul_nonneg he m)))
      (hvm.trans (le_add_of_nonneg_left (nsmul_nonneg he n)))
  have hbound : BddAbove (norm '' s) := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact al_norm_mono hy.1 hy.2.1
  obtain ⟨b, hb, u, hu, hlim, _⟩ :=
    al_exists_isLUB_of_directed_norm_bdd hAL hs hpos hdir hbound
  have hb0 : 0 ≤ b := hb.1 ⟨le_rfl, hx, 0, by simp⟩
  have hbx : b ≤ x := hb.2 (fun _ hy => hy.2.1)
  have hres : 0 ≤ x-b := sub_nonneg.mpr hbx
  have hzero (z : E) (hz : 0 ≤ z) (hzr : z ≤ x-b)
      (hzp : ∃ n : ℕ, z ≤ n • e) : z = 0 := by
    have hbsub : b ≤ b-z := by
      apply hb.2
      intro y hy
      apply le_sub_iff_add_le.mpr
      apply hb.1
      obtain ⟨n, hn⟩ := hy.2.2
      obtain ⟨m, hm⟩ := hzp
      refine ⟨add_nonneg hy.1 hz, ?_, n+m, ?_⟩
      · calc
          y+z ≤ b+(x-b) := add_le_add (hb.1 hy) hzr
          _ = x := by abel
      · simpa only [add_nsmul] using add_le_add hn hm
    exact le_antisymm (by simpa using le_sub_iff_add_le.mp hbsub) hz
  have her : e ⊓ (x-b) = 0 :=
    hzero _ (le_inf he hres) inf_le_right ⟨1, by simp⟩
  have hrD : x-b ∈ latticeDisjointComplement {e} := by
    intro y hy
    have hy' : y = e := hy
    rw [hy', abs_of_nonneg hres, abs_of_nonneg he, inf_comm]
    exact her
  have hxr : x ⊓ (x-b) = 0 := by
    have h := hxB (x-b) hrD
    simpa only [abs_of_nonneg hx, abs_of_nonneg hres] using h
  have hbeq : b = x := by
    have hresle : x-b ≤ x := sub_le_self x hb0
    rw [inf_eq_right.mpr hresle] at hxr
    exact (sub_eq_zero.mp hxr).symm
  rw [← hbeq]
  apply (positiveFragmentSpan e).isClosed_topologicalClosure.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  exact mem_fragmentSpan_closure_of_nonneg_le_nsmul he (hu n).1
    (hu n).2.2.choose (hu n).2.2.choose_spec

theorem positiveFragmentSpan_closure_eq_principalBand {e : E} (he : 0 ≤ e) :
    (positiveFragmentSpan e).topologicalClosure = principalBand e := by
  apply le_antisymm
  · exact (positiveFragmentSpan e).topologicalClosure_minimal
      (positiveFragmentSpan_le_principalBand e) (isClosed_principalBand e)
  · intro x hx
    have hp := mem_fragmentSpan_closure_of_principalBand_nonneg hAL he (posPart_nonneg x)
      ((principalBand_orderClosed e).posPart_mem hx)
    have hn := mem_fragmentSpan_closure_of_principalBand_nonneg hAL he (negPart_nonneg x)
      ((principalBand_orderClosed e).negPart_mem hx)
    have h := (positiveFragmentSpan e).topologicalClosure.sub_mem hp hn
    rwa [posPart_sub_negPart] at h

end ThesisCommon
