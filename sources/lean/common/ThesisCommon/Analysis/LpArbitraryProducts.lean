import ThesisCommon.Analysis.LpOperators
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Exact finite-p flattening over arbitrary index sets. Tonelli's theorem
identifies the sum of the inner pth powers with the product-index sum.
No countability hypothesis is used in the construction.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Δ Ε Ζ Γ : Type*}
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Reindexing from Δ to Ε reads the source coordinate e⁻¹(j). Both
directions contract, including for p=infinity and empty index types. -/
def lpReindexIsometry (e : Δ ≃ Ε) :
    lp (fun _ : Δ => X) p ≃ₗᵢ[𝕜] lp (fun _ : Ε => X) p where
  toFun := lpRestrict (𝕜 := 𝕜) p e.symm.toEmbedding
  invFun := lpRestrict (𝕜 := 𝕜) p e.toEmbedding
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := by intro x; apply lp.ext; funext i; exact congrArg x (e.symm_apply_apply i)
  right_inv := by intro x; apply lp.ext; funext j; exact congrArg x (e.apply_symm_apply j)
  norm_map' := by
    intro x
    have hR (a : Δ ≃ Ε) (z : lp (fun _ : Δ => X) p) :
        ‖lpRestrict (𝕜 := 𝕜) p a.symm.toEmbedding z‖ ≤ ‖z‖ := by
      exact ((lpRestrict (𝕜 := 𝕜) p a.symm.toEmbedding).le_opNorm z).trans
        (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
          (norm_lpRestrict_le (𝕜 := 𝕜) (X := X) (p := p) a.symm.toEmbedding) (norm_nonneg z)))
    apply (hR e x).antisymm
    have h := (lpRestrict (𝕜 := 𝕜) p e.toEmbedding).le_opNorm
      (lpRestrict (𝕜 := 𝕜) p e.symm.toEmbedding x)
    have heq : lpRestrict (𝕜 := 𝕜) p e.toEmbedding
        (lpRestrict (𝕜 := 𝕜) p e.symm.toEmbedding x) = x := by
      apply lp.ext
      funext i
      exact congrArg x (e.symm_apply_apply i)
    rw [heq] at h
    exact h.trans (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (norm_lpRestrict_le (𝕜 := 𝕜) (X := X) (p := p) e.toEmbedding) (norm_nonneg _)))

@[simp] theorem lpReindexIsometry_apply (e : Δ ≃ Ε)
    (x : lp (fun _ : Δ => X) p) (j : Ε) :
    lpReindexIsometry (𝕜 := 𝕜) p e x j = x (e.symm j) := rfl

@[simp] theorem lpReindexIsometry_symm_apply (e : Δ ≃ Ε)
    (x : lp (fun _ : Ε => X) p) (i : Δ) :
    (lpReindexIsometry (𝕜 := 𝕜) p e).symm x i = x (e i) := rfl

def productCoordinateEmbedding (φ : Δ × Ε ≃ Ζ) (i : Δ) : Ε ↪ Ζ where
  toFun j := φ (i, j)
  inj' := fun _ _ h => congrArg Prod.snd (φ.injective h)

variable (hp : 0 < p.toReal) (φ : Δ × Ε ≃ Ζ)

include hp in
theorem lp_arbitrary_pair_summable
    (x : lp (fun _ : Δ => lp (fun _ : Ε => X) p) p) :
    Summable (fun ij : Δ × Ε => ‖x ij.1 ij.2‖ ^ p.toReal) := by
  apply (summable_prod_of_nonneg (fun ij => Real.rpow_nonneg (norm_nonneg _) _)).mpr
  refine ⟨fun i => (lp.memℓp (x i)).summable hp, ?_⟩
  exact ((lp.memℓp x).summable hp).congr (fun i => lp.norm_rpow_eq_tsum hp (x i))

def lpProductFlattenValue
    (x : lp (fun _ : Δ => lp (fun _ : Ε => X) p) p) : lp (fun _ : Ζ => X) p :=
  ⟨fun z => x (φ.symm z).1 (φ.symm z).2,
    memℓp_gen ((φ.symm.summable_iff
      (f := fun ij : Δ × Ε => ‖x ij.1 ij.2‖ ^ p.toReal)).mpr
        (lp_arbitrary_pair_summable p hp x))⟩

theorem norm_lpProductFlattenValue
    (x : lp (fun _ : Δ => lp (fun _ : Ε => X) p) p) :
    ‖lpProductFlattenValue p hp φ x‖ = ‖x‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp
  calc
    _ = ∑' z, ‖x (φ.symm z).1 (φ.symm z).2‖ ^ p.toReal := lp.norm_rpow_eq_tsum hp _
    _ = ∑' ij : Δ × Ε, ‖x ij.1 ij.2‖ ^ p.toReal :=
      φ.symm.tsum_eq (fun ij : Δ × Ε => ‖x ij.1 ij.2‖ ^ p.toReal)
    _ = ∑' i, ∑' j, ‖x i j‖ ^ p.toReal := (lp_arbitrary_pair_summable p hp x).tsum_prod
    _ = ∑' i, ‖x i‖ ^ p.toReal :=
      tsum_congr (fun i => (lp.norm_rpow_eq_tsum hp (x i)).symm)
    _ = ‖x‖ ^ p.toReal := (lp.norm_rpow_eq_tsum hp x).symm

def lpProductUnflattenValue (x : lp (fun _ : Ζ => X) p) :
    lp (fun _ : Δ => lp (fun _ : Ε => X) p) p :=
  ⟨fun i => lpRestrict (𝕜 := 𝕜) p (productCoordinateEmbedding φ i) x, by
    apply memℓp_gen
    have hpair : Summable (fun ij : Δ × Ε => ‖x (φ ij)‖ ^ p.toReal) :=
      (φ.summable_iff (f := fun z => ‖x z‖ ^ p.toReal)).mpr ((lp.memℓp x).summable hp)
    have hs := ((summable_prod_of_nonneg (fun ij : Δ × Ε =>
      Real.rpow_nonneg (norm_nonneg (x (φ ij))) _)).mp hpair).2
    exact hs.congr (fun i => (lp.norm_rpow_eq_tsum hp
      (lpRestrict (𝕜 := 𝕜) p (productCoordinateEmbedding φ i) x)).symm)⟩

/-- Flatten the actual iterated ℓp norm along any supplied product bijection. -/
def lpProductFlattenIsometry :
    lp (fun _ : Δ => lp (fun _ : Ε => X) p) p ≃ₗᵢ[𝕜] lp (fun _ : Ζ => X) p where
  toFun := lpProductFlattenValue p hp φ
  invFun := lpProductUnflattenValue (𝕜 := 𝕜) p hp φ
  map_add' := by intros; apply lp.ext; funext z; rfl
  map_smul' := by intros; apply lp.ext; funext z; rfl
  left_inv := by
    intro x
    apply lp.ext
    funext i
    apply lp.ext
    funext j
    change x (φ.symm (φ (i, j))).1 (φ.symm (φ (i, j))).2 = x i j
    rw [φ.symm_apply_apply]
  right_inv := by
    intro x
    apply lp.ext
    funext z
    change x (φ ((φ.symm z).1, (φ.symm z).2)) = x z
    simp only [Prod.mk.eta, φ.apply_symm_apply]
  norm_map' := norm_lpProductFlattenValue p hp φ

@[simp] theorem lpProductFlattenIsometry_apply
    (x : lp (fun _ : Δ => lp (fun _ : Ε => X) p) p) (z : Ζ) :
    lpProductFlattenIsometry (𝕜 := 𝕜) p hp φ x z = x (φ.symm z).1 (φ.symm z).2 := rfl

@[simp] theorem lpProductFlattenIsometry_apply_image
    (x : lp (fun _ : Δ => lp (fun _ : Ε => X) p) p) (i : Δ) (j : Ε) :
    lpProductFlattenIsometry (𝕜 := 𝕜) p hp φ x (φ (i, j)) = x i j := by
  simp only [lpProductFlattenIsometry_apply, φ.symm_apply_apply]

@[simp] theorem lpProductFlattenIsometry_symm_apply
    (x : lp (fun _ : Ζ => X) p) (i : Δ) (j : Ε) :
    (lpProductFlattenIsometry (𝕜 := 𝕜) p hp φ).symm x i j = x (φ (i, j)) := rfl

/-- Cardinal multiplication by aleph-zero is realized by an actual bijection. -/
def infiniteCountableProductEquiv (Γ : Type*) [Infinite Γ] : Γ × ℕ ≃ Γ := by
  apply Classical.choice
  apply Cardinal.eq.mp
  simpa only [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0]
    using (Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk Γ))

def lpArbitraryAbsorbCountableIsometry [Infinite Γ] :
    lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p ≃ₗᵢ[𝕜] lp (fun _ : Γ => X) p :=
  lpProductFlattenIsometry p hp (infiniteCountableProductEquiv Γ)

def lpArbitrarySequenceSelfIsometry [Infinite Γ] :
    lp (fun _ : Γ => X) p ≃ₗᵢ[𝕜] lp (fun _ : ℕ => lp (fun _ : Γ => X) p) p :=
  (lpProductFlattenIsometry p hp
    ((Equiv.prodComm ℕ Γ).trans (infiniteCountableProductEquiv Γ))).symm

end ThesisCommon
