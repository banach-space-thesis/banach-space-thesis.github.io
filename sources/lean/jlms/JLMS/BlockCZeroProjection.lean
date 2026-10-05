import JLMS.DualFiniteBlocks

/-!
# Galego–Plichko projection from normalized weak-star-null blocks

The analytic block-existence theorem is an explicit input here. Once the
blocks are given, coordinate extension, phase vectors, disjoint synthesis,
and a weak-star sequence operator construct an exact factorization. The
outgoing norm is at most 1/c and the incoming norm at most one. No distortion
theorem is needed when the original embedding already has lower bound c.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Every bounded sequence of dual functionals admits normalized finite,
pairwise disjoint coefficient blocks converging pointwise to zero. This is
the precise Hagler–Johnson consequence required below; existence is not
asserted until separately proved. -/
def DualNormalizedBlockNull : Prop :=
  ∀ f : ℕ → (X →L[𝕜] 𝕜), (∃ C : ℝ, ∀ n, ‖f n‖ ≤ C) →
    ∃ F : ℕ → Finset ℕ, ∃ a : ℕ → ℕ → 𝕜,
      (Pairwise fun n m => Disjoint (F n) (F m)) ∧
      (∀ n, ∑ k ∈ F n, ‖a n k‖ = 1) ∧
      ∀ x, Tendsto (fun n => dualFiniteBlock f (F n) (a n) x) atTop (𝓝 0)

theorem exists_cZero_projection_of_blocks (hX : DualNormalizedBlockNull (𝕜 := 𝕜) (X := X))
    (J : cZero 𝕜 →L[𝕜] X) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    ∃ U : X →L[𝕜] cZero 𝕜, ∃ A : cZero 𝕜 →L[𝕜] cZero 𝕜,
      (U.comp J).comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ ≤ 1 / c ∧ ‖A‖ ≤ 1 := by
  obtain ⟨f, hf, hcoord⟩ := exists_cZero_coordinateExtensions J hc hlower
  obtain ⟨F, a, hF, ha, ht⟩ := hX f ⟨1 / c, hf⟩
  let g (n : ℕ) := dualFiniteBlock f (F n) (a n)
  have hg (n : ℕ) : ‖g n‖ ≤ 1 / c := norm_dualFiniteBlock_le f (F n) (a n) hf (ha n)
  let U := weakStarSequenceOperator g (1 / c) (one_div_pos.mpr hc).le hg ht
  let A := cZeroFiniteBlockInsertion (𝕜 := 𝕜) F hF a
  refine ⟨U, A, ?_, norm_weakStarSequenceOperator_le _ _ _ _ _, norm_cZeroFiniteBlockInsertion_le _ _ _⟩
  apply cZero_operator_eq_of_units
  intro m
  ext n
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    A, cZeroFiniteBlockInsertion_unit, U, weakStarSequenceOperator_apply, g,
    dualFiniteBlock_phase_pair J f hcoord F hF a ha, cZeroUnit_apply]
  split_ifs <;> simp_all

end JLMS
