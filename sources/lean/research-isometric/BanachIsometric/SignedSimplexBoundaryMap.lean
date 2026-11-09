import BanachIsometric.SimplexBoundarySphereLipschitz
import BanachIsometric.SignedSimplexCount
import BanachIsometric.LipschitzNormalization
import BanachIsometric.SphereSignedDegreeSurjective

/-! A Lipschitz singular simplex of one higher dimension induces an actual
sphere map by restricting to its boundary and embedding the target coordinates
in the upper hemisphere. The resulting sphere map has degree zero. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric NormedSpace SphereGenerator
open scoped NNReal Topology

def signedUpperVector (d : ℕ) (y : Fin d → ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm (Fin.cons 1 y)

@[simp] theorem signedUpperVector_head (d : ℕ) (y : Fin d → ℝ) :
    signedUpperVector d y 0 = 1 := rfl

theorem signedUpperVector_norm_lower (d : ℕ) (y : Fin d → ℝ) :
    1 ≤ ‖signedUpperVector d y‖ := by
  simpa using PiLp.norm_apply_le (signedUpperVector d y) 0

theorem signedUpperVector_ne_zero (d : ℕ) (y : Fin d → ℝ) : signedUpperVector d y ≠ 0 := by
  intro h
  have hn := signedUpperVector_norm_lower d y
  rw [h, norm_zero] at hn
  norm_num at hn

def signedUpperSphere (d : ℕ) (y : Fin d → ℝ) : Sph d :=
  ⟨normalize (signedUpperVector d y), mem_sphere_zero_iff_norm.mpr
    (norm_normalize (signedUpperVector_ne_zero d y))⟩

theorem signedUpperSphere_head_pos (d : ℕ) (y : Fin d → ℝ) : 0 < (signedUpperSphere d y).val 0 := by
  change 0 < ‖signedUpperVector d y‖⁻¹ * signedUpperVector d y 0
  rw [signedUpperVector_head, mul_one]
  exact inv_pos.mpr (norm_pos_iff.mpr (signedUpperVector_ne_zero d y))

theorem signedUpperSphere_injective (d : ℕ) : Function.Injective (signedUpperSphere d) := by
  intro x y h
  have he : normalize (signedUpperVector d x) = normalize (signedUpperVector d y) :=
    congrArg Subtype.val h
  have hh := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 1)) => v 0) he
  change ‖signedUpperVector d x‖⁻¹ * 1 = ‖signedUpperVector d y‖⁻¹ * 1 at hh
  simp only [mul_one] at hh
  have hv : signedUpperVector d x = signedUpperVector d y := by
    change ‖signedUpperVector d x‖⁻¹ • signedUpperVector d x =
      ‖signedUpperVector d y‖⁻¹ • signedUpperVector d y at he
    rw [← hh] at he
    exact smul_right_injective _ (inv_ne_zero (norm_ne_zero_iff.mpr (signedUpperVector_ne_zero d x))) he
  funext i
  exact congrArg (fun v : EuclideanSpace ℝ (Fin (d + 1)) => v i.succ) hv

theorem exists_lipschitz_signedUpperSphere (d : ℕ) :
    ∃ K : ℝ≥0, LipschitzWith K (signedUpperSphere d) := by
  let e := (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm
  have hcons : LipschitzWith 1 (fun x : Fin d → ℝ => Fin.cons (α := fun _ => ℝ) 1 x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · change dist (x j) (y j) ≤ dist x y
      exact (dist_pi_le_iff (dist_nonneg (x := x) (y := y))).mp le_rfl j
  have hV : LipschitzWith _ (signedUpperVector d) := e.lipschitz.comp hcons
  have hn := lipschitzWith_normalize_of_lower_bound hV (by norm_num : (0 : ℝ≥0) < 1)
    (fun y => by simpa using signedUpperVector_norm_lower d y)
  exact ⟨_, hn.subtype_mk (fun y => (signedUpperSphere d y).property)⟩

def signedSimplexBoundaryMap (n : ℕ) (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) :
    Sph (n + 1) → Sph (n + 1) := fun u =>
  signedUpperSphere (n + 1) (σ (((simplexBoundarySphereHomeomorph n).symm u).val))

theorem exists_lipschitz_signedSimplexBoundaryMap (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {K : ℝ≥0} (hK : LipschitzWith K σ) :
    ∃ L : ℝ≥0, LipschitzWith L (signedSimplexBoundaryMap n σ) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_signedUpperSphere (n + 1)
  obtain ⟨M, hM⟩ := exists_lipschitz_simplexBoundarySphereHomeomorph_symm n
  exact ⟨_, hL.comp (hK.comp ((LipschitzWith.subtype_val _).comp hM))⟩

theorem signedSimplexBoundaryMap_degree_zero (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {K : ℝ≥0} (hK : LipschitzWith K σ) :
    sphereSignedDegree (EuclideanSpace.equiv (Fin (n + 2)) ℝ) (signedSimplexBoundaryMap n σ) = 0 := by
  obtain ⟨L, hL⟩ := exists_lipschitz_signedSimplexBoundaryMap n σ hK
  by_contra h
  let a : Sph (n + 1) := ⟨-(signedUpperSphere (n + 1) 0).val, by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_eq_of_mem_sphere (signedUpperSphere (n + 1) 0)]⟩
  obtain ⟨u, hu⟩ := sphereSignedDegree_surjective_of_ne_zero _ hL h a
  have hp := signedUpperSphere_head_pos (n + 1) (σ (((simplexBoundarySphereHomeomorph n).symm u).val))
  change 0 < (signedSimplexBoundaryMap n σ u).val 0 at hp
  rw [hu] at hp
  change 0 < -(signedUpperSphere (n + 1) 0).val 0 at hp
  linarith [signedUpperSphere_head_pos (n + 1) 0]

end BanachIsometric.SingularPrism
