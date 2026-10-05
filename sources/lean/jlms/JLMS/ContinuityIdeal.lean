import JLMS.Definitions
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Ogden Definition 6.13: the continuity ideal

The left and right continuity spaces are defined using continuity of the
actual maps y ↦ θ(xy) and y ↦ θ(yx). Both are vector subspaces and are
stable under multiplication on either side. Their intersection is Ogden's
continuity ideal. No continuity of θ itself is assumed.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

def homLeftLinear (θ : B →ₙₐ[𝕜] A) (x : B) : B →ₗ[𝕜] A where
  toFun y := θ (x * y)
  map_add' y z := by simp [mul_add]
  map_smul' c y := by simp [mul_smul_comm]

def homRightLinear (θ : B →ₙₐ[𝕜] A) (x : B) : B →ₗ[𝕜] A where
  toFun y := θ (y * x)
  map_add' y z := by simp [add_mul]
  map_smul' c y := by simp [smul_mul_assoc]

omit [IsScalarTower 𝕜 B B] in
@[simp] theorem homLeftLinear_apply (θ : B →ₙₐ[𝕜] A) (x y : B) :
    homLeftLinear θ x y = θ (x * y) := rfl

omit [SMulCommClass 𝕜 B B] in
@[simp] theorem homRightLinear_apply (θ : B →ₙₐ[𝕜] A) (x y : B) :
    homRightLinear θ x y = θ (y * x) := rfl

def leftContinuitySpace (θ : B →ₙₐ[𝕜] A) : Submodule 𝕜 B where
  carrier := {x | Continuous (homLeftLinear θ x)}
  zero_mem' := by simpa [homLeftLinear] using (continuous_const : Continuous (fun _ : B => (0 : A)))
  add_mem' := by
    intro x z hx hz
    change Continuous (homLeftLinear θ (x + z))
    convert hx.add hz using 1
    ext y
    simp [homLeftLinear, add_mul]
  smul_mem' := by
    intro c x hx
    change Continuous (homLeftLinear θ (c • x))
    convert (continuous_const : Continuous (fun _ : B => c)).smul hx using 1
    ext y
    simp [homLeftLinear, smul_mul_assoc]

def rightContinuitySpace (θ : B →ₙₐ[𝕜] A) : Submodule 𝕜 B where
  carrier := {x | Continuous (homRightLinear θ x)}
  zero_mem' := by simpa [homRightLinear] using (continuous_const : Continuous (fun _ : B => (0 : A)))
  add_mem' := by
    intro x z hx hz
    change Continuous (homRightLinear θ (x + z))
    convert hx.add hz using 1
    ext y
    simp [homRightLinear, mul_add]
  smul_mem' := by
    intro c x hx
    change Continuous (homRightLinear θ (c • x))
    convert (continuous_const : Continuous (fun _ : B => c)).smul hx using 1
    ext y
    simp [homRightLinear, mul_smul_comm]

def continuityIdeal (θ : B →ₙₐ[𝕜] A) : Submodule 𝕜 B :=
  leftContinuitySpace θ ⊓ rightContinuitySpace θ

@[simp] theorem mem_continuityIdeal (θ : B →ₙₐ[𝕜] A) (x : B) :
    x ∈ continuityIdeal θ ↔
      Continuous (homLeftLinear θ x) ∧ Continuous (homRightLinear θ x) := Iff.rfl

theorem leftContinuitySpace_mul_left (θ : B →ₙₐ[𝕜] A) (a : B)
    {x : B} (hx : x ∈ leftContinuitySpace θ) : a * x ∈ leftContinuitySpace θ := by
  change Continuous (homLeftLinear θ (a * x))
  convert (continuous_const : Continuous (fun _ : B => θ a)).mul hx using 1
  ext y
  simp [homLeftLinear, mul_assoc]

theorem leftContinuitySpace_mul_right (θ : B →ₙₐ[𝕜] A) (a : B)
    {x : B} (hx : x ∈ leftContinuitySpace θ) : x * a ∈ leftContinuitySpace θ := by
  change Continuous (homLeftLinear θ (x * a))
  convert hx.comp ((continuous_const : Continuous (fun _ : B => a)).mul
    (continuous_id : Continuous (fun y : B => y))) using 1
  ext y
  simp [homLeftLinear, mul_assoc]

theorem rightContinuitySpace_mul_left (θ : B →ₙₐ[𝕜] A) (a : B)
    {x : B} (hx : x ∈ rightContinuitySpace θ) : a * x ∈ rightContinuitySpace θ := by
  change Continuous (homRightLinear θ (a * x))
  convert hx.comp ((continuous_id : Continuous (fun y : B => y)).mul
    (continuous_const : Continuous (fun _ : B => a))) using 1
  ext y
  simp [homRightLinear, mul_assoc]

theorem rightContinuitySpace_mul_right (θ : B →ₙₐ[𝕜] A) (a : B)
    {x : B} (hx : x ∈ rightContinuitySpace θ) : x * a ∈ rightContinuitySpace θ := by
  change Continuous (homRightLinear θ (x * a))
  convert hx.mul (continuous_const : Continuous (fun _ : B => θ a)) using 1
  ext y
  simp [homRightLinear, mul_assoc]

theorem continuityIdeal_mul_left (θ : B →ₙₐ[𝕜] A) (a : B)
    {x : B} (hx : x ∈ continuityIdeal θ) : a * x ∈ continuityIdeal θ :=
  ⟨leftContinuitySpace_mul_left θ a hx.1, rightContinuitySpace_mul_left θ a hx.2⟩

theorem continuityIdeal_mul_right (θ : B →ₙₐ[𝕜] A) (a : B)
    {x : B} (hx : x ∈ continuityIdeal θ) : x * a ∈ continuityIdeal θ :=
  ⟨leftContinuitySpace_mul_right θ a hx.1, rightContinuitySpace_mul_right θ a hx.2⟩

end JLMS
