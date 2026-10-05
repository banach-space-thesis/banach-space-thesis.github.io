import JLMS.Minimality
import JLMS.IdentityEssentialNorm

/-!
# Section 8: summing simultaneous factorizations

The series argument in Lemma 8.2 is independent of the concrete c₀ block
decomposition. We prove it for an orthogonal family of retracts aₙ,bₙ, provided
their norms are uniformly bounded and the individual factor maps are summable
in norm. The c₀ block decomposition and its embedding in C₀(K) remain separate
construction tasks.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The block inclusions and projections satisfy the Kronecker-delta identity. -/
structure OrthogonalRetracts (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Z : Type*) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] where
  inclusion : ℕ → Z →L[𝕜] E
  projection : ℕ → E →L[𝕜] Z
  retract : ∀ j, (projection j).comp (inclusion j) = ContinuousLinearMap.id 𝕜 Z
  orthogonal : ∀ i j, i ≠ j → (projection i).comp (inclusion j) = 0
  bound : ℝ
  inclusion_bound : ∀ j, ‖inclusion j‖ ≤ bound
  projection_bound : ∀ j, ‖projection j‖ ≤ bound

namespace OrthogonalRetracts

variable (R : OrthogonalRetracts 𝕜 E Z)

/-- Pₙ in Lemma 8.2. -/
def block (j : ℕ) : E →L[𝕜] E := (R.inclusion j).comp (R.projection j)

omit [CompleteSpace E] in
theorem block_idempotent (j : ℕ) : (R.block j).comp (R.block j) = R.block j := by
  ext x
  exact congrArg (fun S : Z →L[𝕜] Z => R.inclusion j (S (R.projection j x))) (R.retract j)

omit [CompleteSpace E] in
/-- Compactness of a block would imply compactness of the identity on Z. -/
theorem block_noncompact (hZ : ¬ IsCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (j : ℕ) : ¬ IsCompactOperator (R.block j) := by
  intro h
  have hc := (h.comp_clm (R.inclusion j)).clm_comp (R.projection j)
  change IsCompactOperator ((R.projection j).comp ((R.block j).comp (R.inclusion j))) at hc
  have heq : (R.projection j).comp ((R.block j).comp (R.inclusion j)) =
      ContinuousLinearMap.id 𝕜 Z := by
    ext z
    have hr (w : Z) : R.projection j (R.inclusion j w) = w :=
      congrArg (fun S : Z →L[𝕜] Z => S w) (R.retract j)
    exact (hr (R.projection j (R.inclusion j z))).trans (hr z)
  rw [heq] at hc
  exact hZ hc

/-- The two absolutely convergent series in the proof of Lemma 8.2 give a
single simultaneous compression of all Tₙ. -/
theorem exists_simultaneous_of_summable
    (T : ℕ → E →L[𝕜] E) (U : ℕ → E →L[𝕜] Z) (V : ℕ → Z →L[𝕜] E)
    (hfactor : ∀ j, ((U j).comp (T j)).comp (V j) = ContinuousLinearMap.id 𝕜 Z)
    (hU : Summable fun j => ‖U j‖) (hV : Summable fun j => ‖V j‖) :
    ∃ A B : E →L[𝕜] E, ∀ j,
      (((R.block j).comp A).comp (T j)).comp (B.comp (R.block j)) = R.block j := by
  classical
  let a : ℕ → E →L[𝕜] E := fun n => (R.inclusion n).comp (U n)
  let b : ℕ → E →L[𝕜] E := fun n => (V n).comp (R.projection n)
  have ha : Summable a := (hU.mul_left R.bound).of_norm_bounded (fun n =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (R.inclusion_bound n) (norm_nonneg (U n))))
  have hb : Summable b := (hV.mul_right R.bound).of_norm_bounded (fun n =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (R.projection_bound n) (norm_nonneg (V n))))
  have hleft (j : ℕ) : (R.block j).comp (∑' n, a n) = (R.inclusion j).comp (U j) := by
    have hm := (ContinuousLinearMap.compL 𝕜 E E E (R.block j)).map_tsum ha
    change (R.block j).comp (∑' n, a n) = ∑' n, (R.block j).comp (a n) at hm
    rw [hm, tsum_eq_single j]
    · ext x
      exact congrArg (fun S : Z →L[𝕜] Z => R.inclusion j (S (U j x))) (R.retract j)
    · intro n hn
      have ho := R.orthogonal j n (Ne.symm hn)
      ext x
      have hz := congrArg (fun S : Z →L[𝕜] Z => R.inclusion j (S (U n x))) ho
      simpa [block, a] using hz
  have hright (j : ℕ) : (∑' n, b n).comp (R.block j) = (V j).comp (R.projection j) := by
    have hm := ((ContinuousLinearMap.compL 𝕜 E E E).flip (R.block j)).map_tsum hb
    change (∑' n, b n).comp (R.block j) = ∑' n, (b n).comp (R.block j) at hm
    rw [hm, tsum_eq_single j]
    · ext x
      exact congrArg (fun S : Z →L[𝕜] Z => V j (S (R.projection j x))) (R.retract j)
    · intro n hn
      have ho := R.orthogonal n j hn
      ext x
      have hz := congrArg (fun S : Z →L[𝕜] Z => V n (S (R.projection j x))) ho
      simpa [block, b] using hz
  refine ⟨∑' n, a n, ∑' n, b n, ?_⟩
  intro j
  rw [hleft, hright]
  ext x
  exact congrArg (fun S : Z →L[𝕜] Z => R.inclusion j (S (R.projection j x))) (hfactor j)

include R in
/-- A reusable version of the Section 8 minimality theorem: only construction
of the block system and summable individual factorizations remains to supply. -/
theorem essentialNormIsMinimal_of_summable_factorizations
    (hZ : ¬ IsCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (M : ℕ → ℝ) (hM : ∀ j, 0 < M j)
    (hfactor : ∀ T : ℕ → E →L[𝕜] E, (∀ j, M j < essentialNorm (T j)) →
      ∃ U : ℕ → E →L[𝕜] Z, ∃ V : ℕ → Z →L[𝕜] E,
        (∀ j, ((U j).comp (T j)).comp (V j) = ContinuousLinearMap.id 𝕜 Z) ∧
        (Summable fun j => ‖U j‖) ∧ (Summable fun j => ‖V j‖)) :
    EssentialNormIsMinimal 𝕜 E := by
  apply essentialNormIsMinimal_of_simultaneous R.block M hM R.block_idempotent
    (R.block_noncompact hZ)
  intro T hT
  obtain ⟨U, V, hUV, hU, hV⟩ := hfactor T hT
  exact R.exists_simultaneous_of_summable T U V hUV hU hV

end OrthogonalRetracts

end JLMS
