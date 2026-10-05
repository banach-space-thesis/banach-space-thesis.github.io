import ThesisCommon.Analysis.LpFamilyDiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Exact finite-p flattening and reindexing for genuinely varying fibres. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 ι κ ν : Type*} [RCLike 𝕜] {E : κ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)

include hp in
theorem lp_family_pair_summable (x : lp (fun _ : ι => lp E p) p) :
    Summable (fun ij : ι × κ => ‖x ij.1 ij.2‖ ^ p.toReal) := by
  apply (summable_prod_of_nonneg (fun ij => Real.rpow_nonneg (norm_nonneg _) _)).mpr
  refine ⟨fun i => (lp.memℓp (x i)).summable hp, ?_⟩
  exact ((lp.memℓp x).summable hp).congr (fun i => lp.norm_rpow_eq_tsum hp (x i))

def lpFamilyFlattenValue (x : lp (fun _ : ι => lp E p) p) :
    lp (fun ij : ι × κ => E ij.2) p :=
  ⟨fun ij => x ij.1 ij.2, memℓp_gen (lp_family_pair_summable p hp x)⟩

theorem norm_lpFamilyFlattenValue (x : lp (fun _ : ι => lp E p) p) :
    ‖lpFamilyFlattenValue p hp x‖ = ‖x‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp
  calc
    _ = ∑' ij : ι × κ, ‖x ij.1 ij.2‖ ^ p.toReal := lp.norm_rpow_eq_tsum hp _
    _ = ∑' i, ∑' j, ‖x i j‖ ^ p.toReal := (lp_family_pair_summable p hp x).tsum_prod
    _ = ∑' i, ‖x i‖ ^ p.toReal := tsum_congr (fun i => (lp.norm_rpow_eq_tsum hp (x i)).symm)
    _ = ‖x‖ ^ p.toReal := (lp.norm_rpow_eq_tsum hp x).symm

def lpFamilyProductRow (x : lp (fun ij : ι × κ => E ij.2) p) (i : ι) : lp E p :=
  ⟨fun j => x (i,j), memℓp_gen (((lp.memℓp x).summable hp).comp_injective
    (show Function.Injective (fun j : κ => (i,j)) from fun _ _ h => congrArg Prod.snd h))⟩

def lpFamilyUnflattenValue (x : lp (fun ij : ι × κ => E ij.2) p) :
    lp (fun _ : ι => lp E p) p :=
  ⟨lpFamilyProductRow p hp x, by
    apply memℓp_gen
    have hs := ((summable_prod_of_nonneg (fun ij : ι × κ =>
      Real.rpow_nonneg (norm_nonneg (x ij)) _)).mp ((lp.memℓp x).summable hp)).2
    exact hs.congr (fun i => (lp.norm_rpow_eq_tsum hp (lpFamilyProductRow p hp x i)).symm)⟩

def lpFamilyProductFlattenIsometry :
    lp (fun _ : ι => lp E p) p ≃ₗᵢ[𝕜] lp (fun ij : ι × κ => E ij.2) p where
  toFun := lpFamilyFlattenValue p hp
  invFun := lpFamilyUnflattenValue p hp
  map_add' := by intros; apply lp.ext; funext ij; rfl
  map_smul' := by intros; apply lp.ext; funext ij; rfl
  left_inv := by intro x; apply lp.ext; funext i; apply lp.ext; funext j; rfl
  right_inv := by intro x; apply lp.ext; funext ij; rfl
  norm_map' := norm_lpFamilyFlattenValue p hp

@[simp] theorem lpFamilyProductFlattenIsometry_apply (x : lp (fun _ : ι => lp E p) p)
    (i : ι) (j : κ) : lpFamilyProductFlattenIsometry (𝕜 := 𝕜) p hp x (i,j) = x i j := rfl

def lpFamilyReindexValue (e : κ ≃ ν) (x : lp E p) : lp (fun j => E (e.symm j)) p :=
  ⟨fun j => x (e.symm j), memℓp_gen
    ((e.symm.summable_iff (f := fun i => ‖x i‖ ^ p.toReal)).mpr ((lp.memℓp x).summable hp))⟩

def lpFamilyUnreindexValue (e : κ ≃ ν) (y : lp (fun j => E (e.symm j)) p) : lp E p :=
  ⟨(Equiv.piCongrLeft' E e).symm y, by
    apply memℓp_gen
    apply (e.symm.summable_iff (f := fun i => ‖(Equiv.piCongrLeft' E e).symm y i‖ ^ p.toReal)).mp
    simpa only [Function.comp_def, Equiv.piCongrLeft'_symm_apply_apply] using (lp.memℓp y).summable hp⟩

theorem norm_lpFamilyReindexValue (e : κ ≃ ν) (x : lp E p) :
    ‖lpFamilyReindexValue p hp e x‖ = ‖x‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp
  calc
    _ = ∑' j, ‖x (e.symm j)‖ ^ p.toReal := lp.norm_rpow_eq_tsum hp _
    _ = ∑' i, ‖x i‖ ^ p.toReal := e.symm.tsum_eq (fun i => ‖x i‖ ^ p.toReal)
    _ = ‖x‖ ^ p.toReal := (lp.norm_rpow_eq_tsum hp x).symm

def lpFamilyReindexIsometry (e : κ ≃ ν) :
    lp E p ≃ₗᵢ[𝕜] lp (fun j => E (e.symm j)) p where
  toFun := lpFamilyReindexValue p hp e
  invFun := lpFamilyUnreindexValue p hp e
  map_add' := by intros; apply lp.ext; funext j; rfl
  map_smul' := by intros; apply lp.ext; funext j; rfl
  left_inv := by
    intro x
    apply lp.ext
    exact (Equiv.piCongrLeft' E e).symm_apply_apply x
  right_inv := by
    intro y
    apply lp.ext
    exact (Equiv.piCongrLeft' E e).apply_symm_apply y
  norm_map' := norm_lpFamilyReindexValue p hp e

@[simp] theorem lpFamilyReindexIsometry_apply (e : κ ≃ ν) (x : lp E p) (j : ν) :
    lpFamilyReindexIsometry (𝕜 := 𝕜) p hp e x j = x (e.symm j) := rfl

def lpFamilyProductReindexIsometry (e : ι × κ ≃ ν) :
    lp (fun _ : ι => lp E p) p ≃ₗᵢ[𝕜] lp (fun j => E (e.symm j).2) p :=
  (lpFamilyProductFlattenIsometry (𝕜 := 𝕜) p hp).trans (lpFamilyReindexIsometry p hp e)

end ThesisCommon
