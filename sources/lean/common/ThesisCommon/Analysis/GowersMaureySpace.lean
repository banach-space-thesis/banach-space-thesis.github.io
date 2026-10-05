import ThesisCommon.Analysis.GowersMaureyImplicitNorm
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Analysis.Normed.Module.Completion

/-! Actual completion of c₀₀ with the shift-generated Gowers--Maurey norm.
The admissible construction choices remain explicit. Primeness and the
operator-algebra quotient are not fields or assumptions of this space.
-/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

set_option linter.unusedVariables false in
/-- Fresh finite-sequence type, carrying the implicit norm. -/
def PreSpace (D : ConstructionData 𝕜) := C00 𝕜

namespace PreSpace
variable {D : ConstructionData 𝕜}

instance : AddCommGroup (PreSpace D) := inferInstanceAs (AddCommGroup (C00 𝕜))
instance : Module 𝕜 (PreSpace D) := inferInstanceAs (Module 𝕜 (C00 𝕜))

def coefficients (x : PreSpace D) : C00 𝕜 := x

instance : CoeFun (PreSpace D) (fun _ => ℕ → 𝕜) := ⟨fun x => coefficients x⟩

@[ext] theorem ext {x y : PreSpace D} (h : ∀ n, x n = y n) : x = y := Finsupp.ext h

instance : NormedAddCommGroup (PreSpace D) :=
  AddGroupNorm.toNormedAddCommGroup
    { (implicitNorm D).toAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun _ h => implicitNorm_eq_zero D h }

instance : NormedSpace 𝕜 (PreSpace D) where
  norm_smul_le c x := (map_smul_eq_mul (implicitNorm D) c x).le

theorem norm_def (x : PreSpace D) : ‖x‖ = implicitNorm D (coefficients x) := rfl

theorem norm_apply_le (x : PreSpace D) (n : ℕ) : ‖x n‖ ≤ ‖x‖ :=
  coordinate_le_implicitNorm D x n

def single (n : ℕ) (c : 𝕜) : PreSpace D := Finsupp.single n c

@[simp] theorem single_apply (n m : ℕ) (c : 𝕜) :
    single (D := D) n c m = if n = m then c else 0 := Finsupp.single_apply

@[simp] theorem norm_single (n : ℕ) (c : 𝕜) : ‖single (D := D) n c‖ = ‖c‖ :=
  implicitNorm_single D n c

instance : Nontrivial (PreSpace D) := by
  refine ⟨⟨single 0 1, 0, ?_⟩⟩
  intro h
  have hn := norm_single (D := D) 0 (1 : 𝕜)
  rw [h, norm_zero, norm_one] at hn
  exact zero_ne_one hn

/-- Every source tail spread acts contractively on the actual pre-space. -/
def spreadOperator (m n : ℕ) : PreSpace D →L[𝕜] PreSpace D :=
  (spread (𝕜 := 𝕜) m n).mkContinuous 1 (fun x => by
    simpa only [one_mul] using implicitNorm_spread_le D m n x)

theorem norm_spreadOperator_le (m n : ℕ) : ‖spreadOperator (D := D) m n‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

end PreSpace

/-- The Banach space in the shift-generated construction of §4.2/Theorem 13. -/
abbrev ShiftSpace (D : ConstructionData 𝕜) := UniformSpace.Completion (PreSpace D)

def denseEmbedding (D : ConstructionData 𝕜) : PreSpace D →ₗᵢ[𝕜] ShiftSpace D :=
  UniformSpace.Completion.toComplₗᵢ

instance shiftSpace_nontrivial (D : ConstructionData 𝕜) : Nontrivial (ShiftSpace D) :=
  (denseEmbedding D).injective.nontrivial

theorem denseEmbedding_denseRange (D : ConstructionData 𝕜) : DenseRange (denseEmbedding D) :=
  UniformSpace.Completion.denseRange_coe

@[simp] theorem denseEmbedding_norm (D : ConstructionData 𝕜) (x : PreSpace D) :
    ‖denseEmbedding D x‖ = ‖x‖ := (denseEmbedding D).norm_map x

end ThesisCommon.GowersMaurey
