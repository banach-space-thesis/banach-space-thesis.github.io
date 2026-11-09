import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Basic

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.NormedStarDirectLimit
universe u v
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {A : ι → Type v} [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra ℂ (A i)]
variable [∀ i, StarRing (A i)]

variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (f · · ·)]

/-- Isometric maps ensure that a representative's norm is independent
of the stage in which it is computed. -/
class PreservesNorm : Prop where
  norm_map : ∀ i j hij x, ‖f i j hij x‖ = ‖x‖

/-- Keep the norm topology separate from the raw quotient topology. -/
def Carrier := DirectLimit A f

instance ring : Ring (Carrier f) :=
  inferInstanceAs (Ring (DirectLimit A f))

instance module : Module ℂ (Carrier f) :=
  inferInstanceAs (Module ℂ (DirectLimit A f))

def of (i : ι) (x : A i) : Carrier f := ⟦⟨i, x⟩⟧

variable [PreservesNorm f]

def rawNorm : Carrier f → ℝ :=
  Quotient.lift (fun x : Σ i, A i => ‖x.2‖) (by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, hik, hjk, h⟩
    calc
      ‖x‖ = ‖f i k hik x‖ := (PreservesNorm.norm_map (f := f) i k hik x).symm
      _ = ‖f j k hjk y‖ := congrArg norm h
      _ = ‖y‖ := PreservesNorm.norm_map (f := f) j k hjk y)

@[simp] theorem rawNorm_of (i : ι) (x : A i) : rawNorm f (of f i x) = ‖x‖ := rfl

instance normedAddCommGroup : NormedAddCommGroup (Carrier f) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := rawNorm f
      map_zero' := by
        let i : ι := Classical.arbitrary ι
        rw [DirectLimit.zero_def i]
        exact norm_zero
      neg' := DirectLimit.induction f (fun i x => by
        rw [DirectLimit.neg_def]
        exact norm_neg x)
      add_le' := DirectLimit.induction₂ f (fun i x y => by
        rw [DirectLimit.add_def]
        exact norm_add_le x y)
      eq_zero_of_map_eq_zero' := DirectLimit.induction f (fun i x hx => by
        have hx' : x = 0 := norm_eq_zero.mp hx
        rw [hx', DirectLimit.zero_def i]) }

@[simp] theorem norm_of (i : ι) (x : A i) : ‖of f i x‖ = ‖x‖ := rfl

@[simp] theorem smul_of (i : ι) (c : ℂ) (x : A i) :
    c • of f i x = of f i (c • x) := rfl

theorem one_def (i : ι) : (1 : Carrier f) = of f i 1 := DirectLimit.one_def i

instance normedRing : NormedRing (Carrier f) where
  __ := (inferInstance : Ring (Carrier f))
  __ := normedAddCommGroup f
  norm_mul_le := DirectLimit.induction₂ f (fun i x y => by
    rw [DirectLimit.mul_def]
    exact norm_mul_le x y)

@[simp] theorem mul_of (i : ι) (x y : A i) :
    of f i x * of f i y = of f i (x * y) := DirectLimit.mul_def i x y

instance algebra : Algebra ℂ (Carrier f) :=
  Algebra.ofModule
    (fun c => DirectLimit.induction₂ f (fun i x y => by
      rw [DirectLimit.smul_def, DirectLimit.mul_def, DirectLimit.mul_def,
        DirectLimit.smul_def, smul_mul_assoc]))
    (fun c => DirectLimit.induction₂ f (fun i x y => by
      rw [DirectLimit.smul_def, DirectLimit.mul_def, DirectLimit.mul_def,
        DirectLimit.smul_def, mul_smul_comm]))

instance normedAlgebra : NormedAlgebra ℂ (Carrier f) where
  norm_smul_le c := DirectLimit.induction f (fun i x => by
    rw [DirectLimit.smul_def]
    exact norm_smul_le c x)

def starMap : Carrier f → Carrier f :=
  DirectLimit.map f f (fun _ => star) (fun i j hij x => map_star (f i j hij) x)

theorem starMap_of (i : ι) (x : A i) : starMap f (of f i x) = of f i (star x) := rfl

instance starRing : StarRing (Carrier f) where
  star := starMap f
  star_involutive := DirectLimit.induction f (fun i x => by
    change of f i (star (star x)) = of f i x
    rw [star_star])
  star_mul := DirectLimit.induction₂ f (fun i x y => by
    change starMap f ((⟦⟨i, x⟩⟧ : Carrier f) * ⟦⟨i, y⟩⟧) =
      (⟦⟨i, star y⟩⟧ : Carrier f) * ⟦⟨i, star x⟩⟧
    rw [DirectLimit.mul_def, DirectLimit.mul_def]
    exact congrArg (of f i) (star_mul x y))
  star_add := DirectLimit.induction₂ f (fun i x y => by
    change starMap f ((⟦⟨i, x⟩⟧ : Carrier f) + ⟦⟨i, y⟩⟧) =
      (⟦⟨i, star x⟩⟧ : Carrier f) + ⟦⟨i, star y⟩⟧
    rw [DirectLimit.add_def, DirectLimit.add_def]
    exact congrArg (of f i) (star_add x y))

@[simp] theorem star_of (i : ι) (x : A i) : star (of f i x) = of f i (star x) := rfl

instance [∀ i, StarModule ℂ (A i)] : StarModule ℂ (Carrier f) where
  star_smul c := DirectLimit.induction f (fun i x => by
    change star (c • of f i x) = star c • of f i (star x)
    rw [smul_of, star_of, smul_of, star_smul])

instance [∀ i, CStarRing (A i)] : CStarRing (Carrier f) where
  norm_mul_self_le := DirectLimit.induction f (fun i x => by
    change ‖x‖ * ‖x‖ ≤ ‖(of f i (star x) : Carrier f) * of f i x‖
    rw [mul_of, norm_of]
    exact CStarRing.norm_mul_self_le x)

instance [∀ i, NormOneClass (A i)] : NormOneClass (Carrier f) where
  norm_one := by
    let i : ι := Classical.arbitrary ι
    rw [one_def f i, norm_of]
    exact (norm_one : ‖(1 : A i)‖ = 1)

def embedding (i : ι) : A i →⋆ₐ[ℂ] Carrier f where
  __ := DirectLimit.Ring.of A f i
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change of f i (c • 1) = c • (1 : Carrier f)
    rw [DirectLimit.one_def i, DirectLimit.smul_def]
    rfl
  map_star' _ := rfl

end NonCalkinAlgebra.NormedStarDirectLimit
