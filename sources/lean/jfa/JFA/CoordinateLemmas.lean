import JFA.ScalarCoefficient
import JFA.SeparableSubspace
import JFA.TensorSlices
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.HeineCantor

/-! The numbered coordinate lemmas of Section 3, for the actual C(M,X) codomain. -/

noncomputable section
open Set TopologicalSpace
open scoped TensorProduct
namespace JFA
universe u

section Coordinates
variable {𝕜 E X A : Type u} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
variable {M : Type*} [MetricSpace M] [CompactSpace M]
variable (α : UniformCrossnorm 𝕜) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
  (hι : IsTensorCompletion 𝕜 E X A (α.normFor E X) ι)
  (T : A →L[𝕜] C(M, X))

/-- The paper's coordinate πₖ T ιₑ. -/
def paperCoordinate (e : E) (k : M) : X →L[𝕜] X :=
  (ContinuousMap.evalCLM 𝕜 k).comp (T.comp (completionPureMap (α.normFor E X) ι hι e))

variable (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)

/-- The paper's Yₑ₀, formed using the specified set M₀. -/
def paperCoordinateSubspace (E₀ : Set E) (M₀ : Set M) : Submodule 𝕜 X :=
  (Submodule.span 𝕜
    (⋃ i : E₀ × M₀, Set.range (scalarRemainder hX hfew
      (paperCoordinate α ι hι T i.1 i.2)))).topologicalClosure

omit [CompleteSpace X] in
private theorem unit_annihilator (hX : ¬ SeparableSpace X) (Y : Submodule 𝕜 X)
    (hY : IsClosed (Y : Set X)) (hsep : IsSeparable (Y : Set X)) :
    ∃ (x : X) (φ : X →L[𝕜] 𝕜), ‖x‖ ≤ 1 ∧ ‖φ‖ ≤ 1 ∧
      φ x = ((1 / 2 : ℝ) : 𝕜) ∧ ∀ y ∈ Y, φ y = 0 := by
  letI : IsClosed (Y : Set X) := hY
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ Y := by
    by_contra! h
    exact hX (isSeparable_univ_iff.mp (hsep.mono (fun x _ => h x)))
  let z : X ⧸ Y := Submodule.Quotient.mk y
  have hz : z ≠ 0 := fun h => hy ((Submodule.Quotient.mk_eq_zero Y).mp h)
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨g, hg, hgz⟩ := exists_dual_vector 𝕜 z hz
  obtain ⟨w, hw, hwn⟩ := Submodule.Quotient.norm_mk_lt z hzn
  let q : X →L[𝕜] X ⧸ Y := Y.mkQ.mkContinuous 1
    (fun v => by simpa only [one_mul] using Submodule.Quotient.norm_mk_le Y v)
  let a : ℝ := 2 * ‖z‖
  have ha : 0 < a := by dsimp [a]; positivity
  let φ := g.comp q
  have hq : ‖q‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  refine ⟨((a : 𝕜)⁻¹) • w, φ, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos ha, ← div_eq_inv_mul]
    exact (div_le_one₀ ha).mpr (by dsimp [a]; linarith)
  · exact (g.opNorm_comp_le q).trans (by simpa only [hg, one_mul] using hq)
  · have heq : φ w = (‖z‖ : 𝕜) := by
      change g (Submodule.Quotient.mk w) = _
      rw [hw, hgz]
    rw [map_smul, smul_eq_mul, heq, ← RCLike.ofReal_inv, ← RCLike.ofReal_mul]
    congr 1
    dsimp [a]
    field_simp
  · intro v hv
    change g (Submodule.Quotient.mk v) = 0
    rw [(Submodule.Quotient.mk_eq_zero Y).mpr hv, map_zero]

omit [CompactSpace M] in
private theorem paperCoordinateRemainder_mem {E₀ : Set E} {M₀ : Set M}
    {e : E} (he : e ∈ E₀) {k : M} (hk : k ∈ M₀) (x : X) :
    scalarRemainder hX hfew (paperCoordinate α ι hι T e k) x ∈
      paperCoordinateSubspace α ι hι T hX hfew E₀ M₀ :=
  Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_iUnion.mpr ⟨(⟨e, he⟩, ⟨k, hk⟩), x, rfl⟩))

omit [CompactSpace M] in
private theorem paperCoordinate_apply_annihilator (e : E) (k : M) (x : X)
    (φ : X →L[𝕜] 𝕜)
    (hφ : φ (scalarRemainder hX hfew (paperCoordinate α ι hι T e k) x) = 0) :
    φ (T (ι (e ⊗ₜ[𝕜] x)) k) =
      scalarCoefficient hX hfew (paperCoordinate α ι hι T e k) * φ x := by
  change φ (paperCoordinate α ι hι T e k x) = _
  rw [show paperCoordinate α ι hι T e k x =
    scalarCoefficient hX hfew (paperCoordinate α ι hι T e k) • x +
      scalarRemainder hX hfew (paperCoordinate α ι hι T e k) x from
    congrArg (fun B : X →L[𝕜] X => B x) (scalar_decomposition hX hfew _)]
  rw [map_add, hφ, add_zero, map_smul, smul_eq_mul]

/-- Lemma 3.4, including the single vector that works for all choices of
coordinates and scalars for the given finite family. Over ℂ the displayed
inequality for φ(x) means that its value is real and at least 1/2. -/
theorem lemma_3_4 [CompleteSpace A] [SeparableSpace E]
    (M₀ : Set M) (hM₀ : M₀.Countable) (_hd : Dense M₀) :
    (∀ (E₀ : Set E), E₀.Countable →
      ∃ (x : X) (φ : X →L[𝕜] 𝕜), ‖x‖ ≤ 1 ∧ ‖φ‖ ≤ 1 ∧
        (∃ r : ℝ, 1 / 2 ≤ r ∧ φ x = (r : 𝕜)) ∧
        ∀ y ∈ paperCoordinateSubspace α ι hι T hX hfew E₀ M₀, φ y = 0) ∧
    (∀ (n : ℕ) (e : Fin n → E), ∃ x : X, ‖x‖ ≤ 1 ∧
      ∀ (k : Fin n → M₀) (c : Fin n → 𝕜),
        ‖∑ i, c i * scalarCoefficient hX hfew (paperCoordinate α ι hι T (e i) (k i))‖ ≤
          2 * ‖∑ i, c i • T (ι (e i ⊗ₜ[𝕜] x)) (k i)‖) := by
  classical
  have hfirst (E₀ : Set E) (hE₀ : E₀.Countable) :
      ∃ (x : X) (φ : X →L[𝕜] 𝕜), ‖x‖ ≤ 1 ∧ ‖φ‖ ≤ 1 ∧
        φ x = ((1 / 2 : ℝ) : 𝕜) ∧
        ∀ y ∈ paperCoordinateSubspace α ι hι T hX hfew E₀ M₀, φ y = 0 := by
    letI : Countable E₀ := hE₀.to_subtype
    letI : Countable M₀ := hM₀.to_subtype
    apply unit_annihilator hX _ (Submodule.isClosed_topologicalClosure _)
    exact ((IsSeparable.iUnion (fun i : E₀ × M₀ =>
      scalarRemainder_separable hX hfew (paperCoordinate α ι hι T i.1 i.2))).span
        (R := 𝕜)).closure
  constructor
  · intro E₀ hE₀
    obtain ⟨x, φ, hx, hφ, hval, hzero⟩ := hfirst E₀ hE₀
    exact ⟨x, φ, hx, hφ, ⟨1 / 2, le_rfl, hval⟩, hzero⟩
  · intro n e
    obtain ⟨x, φ, hx, hφ, hval, hzero⟩ := hfirst (range e) (countable_range e)
    refine ⟨x, hx, ?_⟩
    intro k c
    have heval (i : Fin n) := paperCoordinate_apply_annihilator α ι hι T hX hfew
      (e i) (k i) x φ (hzero _ (paperCoordinateRemainder_mem α ι hι T hX hfew
        (mem_range_self i) (k i).property x))
    have hsum : φ (∑ i, c i • T (ι (e i ⊗ₜ[𝕜] x)) (k i)) =
        (∑ i, c i * scalarCoefficient hX hfew (paperCoordinate α ι hι T (e i) (k i))) *
          ((1 / 2 : ℝ) : 𝕜) := by
      rw [map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [map_smul, smul_eq_mul, heval i, hval, mul_assoc])
    have hbound := φ.le_of_opNorm_le hφ (∑ i, c i • T (ι (e i ⊗ₜ[𝕜] x)) (k i))
    rw [hsum, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      one_mul] at hbound
    linarith

omit [CompactSpace M] in
private theorem eq_of_eqOn_dense {M₀ : Set M} (hd : Dense M₀)
    {f g : C(M, 𝕜)} (he : Set.EqOn f g M₀) : f = g := by
  ext k
  exact closure_minimal he (isClosed_eq f.continuous g.continuous) (hd k)

/-- Lemma 3.5: uniform continuity on M₀ and existence and uniqueness of the
continuous extension on M. -/
theorem lemma_3_5 [CompleteSpace A] [SeparableSpace E]
    (M₀ : Set M) (hM₀ : M₀.Countable) (hd : Dense M₀) (e : E) :
    UniformContinuous (fun k : M₀ => scalarCoefficient hX hfew
      (paperCoordinate α ι hι T e k)) ∧
    ∃! f : C(M, 𝕜), ∀ k ∈ M₀, f k = scalarCoefficient hX hfew
      (paperCoordinate α ι hι T e k) := by
  obtain ⟨x, φ, _, _, ⟨r, hr, hval⟩, hzero⟩ :=
    (lemma_3_4 α ι hι T hX hfew M₀ hM₀ hd).1 {e} (countable_singleton e)
  let f : C(M, 𝕜) := ⟨fun k => φ (T (ι (e ⊗ₜ[𝕜] x)) k) / (r : 𝕜),
    (φ.continuous.comp (T (ι (e ⊗ₜ[𝕜] x))).continuous).div_const _⟩
  have he (k : M) (hk : k ∈ M₀) :
      f k = scalarCoefficient hX hfew (paperCoordinate α ι hι T e k) := by
    change φ (T (ι (e ⊗ₜ[𝕜] x)) k) / (r : 𝕜) = _
    rw [paperCoordinate_apply_annihilator α ι hι T hX hfew e k x φ
      (hzero _ (paperCoordinateRemainder_mem α ι hι T hX hfew (mem_singleton e) hk x)), hval]
    exact mul_div_cancel_right₀ _ (RCLike.ofReal_ne_zero.mpr (by linarith))
  refine ⟨?_, f, he, fun g hg => eq_of_eqOn_dense hd (fun k hk => (hg k hk).trans (he k hk).symm)⟩
  have h : (fun k : M₀ => scalarCoefficient hX hfew (paperCoordinate α ι hι T e k)) =
      (fun k : M₀ => f k) := funext fun k => (he k k.property).symm
  rw [h]
  exact (CompactSpace.uniformContinuous_of_continuous f.continuous).comp
    uniformContinuous_subtype_val

/-- Lemma 3.6: the uniquely determined extensions of Lemma 3.5 form a
bounded linear operator, with the stated bound 2‖T‖. -/
theorem lemma_3_6 [CompleteSpace A] [SeparableSpace E]
    (M₀ : Set M) (hM₀ : M₀.Countable) (hd : Dense M₀) :
    ∃ U : E →L[𝕜] C(M, 𝕜), ‖U‖ ≤ 2 * ‖T‖ ∧
      ∀ e k, k ∈ M₀ → U e k = scalarCoefficient hX hfew
        (paperCoordinate α ι hι T e k) := by
  choose f hf using fun e => (lemma_3_5 α ι hι T hX hfew M₀ hM₀ hd e).2.exists
  have hnorm (e : E) : ‖f e‖ ≤ ‖T‖ * ‖e‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro k
    apply closure_minimal (s := M₀)
      (t := {k | ‖f e k‖ ≤ ‖T‖ * ‖e‖}) ?_
      (isClosed_le (f e).continuous.norm continuous_const) (hd k)
    intro j hj
    change ‖f e j‖ ≤ _
    rw [hf e j hj]
    refine (scalarCoefficient_norm_le hX hfew _).trans ?_
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro x
    change ‖T (completionPureMap (α.normFor E X) ι hι e x) j‖ ≤ _
    calc
      _ ≤ ‖T (completionPureMap (α.normFor E X) ι hι e x)‖ :=
        ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖T‖ * ‖completionPureMap (α.normFor E X) ι hι e x‖ := T.le_opNorm _
      _ ≤ ‖T‖ * (‖e‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          ((completionPureMap (α.normFor E X) ι hι e).le_of_opNorm_le
            (norm_completionPureMap_le _ _ _ _) x) (norm_nonneg T)
      _ = _ := (mul_assoc _ _ _).symm
  let L : E →ₗ[𝕜] C(M, 𝕜) :=
    { toFun := f
      map_add' := by
        intro e e'
        apply eq_of_eqOn_dense hd
        intro k hk
        change f (e + e') k = f e k + f e' k
        simp only [hf _ _ hk, paperCoordinate, completionPureMap_add,
          ContinuousLinearMap.comp_add, scalarCoefficient_add]
      map_smul' := by
        intro c e
        apply eq_of_eqOn_dense hd
        intro k hk
        change f (c • e) k = c * f e k
        simp only [hf _ _ hk, paperCoordinate, completionPureMap_smul,
          ContinuousLinearMap.comp_smul, scalarCoefficient_smul] }
  let U := L.mkContinuous ‖T‖ hnorm
  exact ⟨U, (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _).trans
    (by linarith [norm_nonneg T]), hf⟩

end Coordinates

/-- Lemma 3.7 for a subspace of C(M,X); the subspace need not be closed. -/
theorem lemma_3_7 {𝕜 X M : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [MetricSpace M] [CompactSpace M]
    (M₀ : Set M) (hM₀ : M₀.Countable) (hd : Dense M₀) (Y : Submodule 𝕜 C(M, X)) :
    IsSeparable (Y : Set C(M, X)) ↔
      ∀ k ∈ M₀, IsSeparable ((fun g : C(M, X) => g k) '' (Y : Set C(M, X))) := by
  constructor
  · exact fun h k _ => h.image (ContinuousMap.evalCLM 𝕜 k).continuous
  · intro h
    letI : Countable M₀ := hM₀.to_subtype
    let Z := (Submodule.span 𝕜 (⋃ k : M₀, (fun g : C(M, X) => g k) ''
      (Y : Set C(M, X)))).topologicalClosure
    have hZ : IsSeparable (Z : Set X) :=
      ((IsSeparable.iUnion fun k : M₀ => h k k.property).span (R := 𝕜)).closure
    letI : SeparableSpace Z := hZ.separableSpace
    let incl : C(M, Z) → C(M, X) := fun g => (⟨Subtype.val, continuous_subtype_val⟩ :
      C(Z, X)).comp g
    have hi : Isometry incl := by
      intro f g
      rw [edist_dist, edist_dist]
      congr 1
    apply (isSeparable_range hi.continuous).mono
    intro g hg
    have hZg : ∀ k, g k ∈ Z := by
      intro k
      apply closure_minimal (s := M₀) (t := g ⁻¹' (Z : Set X)) ?_
        ((Submodule.isClosed_topologicalClosure _).preimage g.continuous) (hd k)
      intro j hj
      exact Submodule.le_topologicalClosure _
        (Submodule.subset_span (mem_iUnion.mpr ⟨⟨j, hj⟩, g, hg, rfl⟩))
    exact ⟨⟨fun k => ⟨g k, hZg k⟩, g.continuous.subtype_mk _⟩, by ext k; rfl⟩

end JFA
