import NonCalkinAlgebra.NormedStarDirectLimit
import NonCalkinAlgebra.NormedStarCompletion
import NonCalkinAlgebra.AFCoefficientStatements

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.NormedStarDirectLimit
open UniformSpace
open scoped NonCalkinAlgebra.NormedStarCompletion
universe u v w

def completionInclusion {B : Type w} [NormedRing B] [NormedAlgebra ℂ B]
    [StarRing B] [NormedStarGroup B] : B →⋆ₐ[ℂ] Completion B where
  __ := Completion.coeRingHom
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change (((c : ℂ) • (1 : B) : B) : Completion B) = c • (1 : Completion B)
    rw [Completion.coe_smul, Completion.coe_one]
  map_star' b := (NormedStarCompletion.star_coe b).symm

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {A : ι → Type v} [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra ℂ (A i)]
variable [∀ i, StarRing (A i)] [∀ i, StarModule ℂ (A i)] [∀ i, CStarRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (f · · ·)] [PreservesNorm f]

abbrev Completed := Completion (Carrier f)

def completedEmbedding (i : ι) : A i →⋆ₐ[ℂ] Completed f :=
  completionInclusion.comp (embedding f i)

@[simp] theorem completedEmbedding_apply (i : ι) (x : A i) :
    completedEmbedding f i x = (of f i x : Completed f) := rfl

theorem completedEmbedding_map {i j : ι} (h : i ≤ j) (x : A i) :
    completedEmbedding f j (f i j h x) = completedEmbedding f i x := by
  simp only [completedEmbedding_apply]
  exact congrArg ((↑) : Carrier f → Completed f)
    ((DirectLimit.eq_of_le ⟨i, x⟩ j h).symm)

theorem completedEmbedding_norm (i : ι) (x : A i) :
    ‖completedEmbedding f i x‖ = ‖x‖ := by
  rw [completedEmbedding_apply, Completion.norm_coe, norm_of]

/-- The completion of a directed system of finite-dimensional stages is
AF with the actual images of those stages as its local subalgebras. -/
theorem completed_AF [∀ i, FiniteDimensional ℂ (A i)] :
    IsApproximatelyFiniteDimensional (Completed f) := by
  let S : Set (StarSubalgebra ℂ (Completed f)) := Set.range fun i => (completedEmbedding f i).range
  refine ⟨S, Set.range_nonempty _, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨(completedEmbedding f k).range, ⟨k, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨f i k hik x, completedEmbedding_map f hik x⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨f j k hjk x, completedEmbedding_map f hjk x⟩
  · rintro _ ⟨i, rfl⟩
    apply FiniteDimensional.of_surjective (completedEmbedding f i).rangeRestrict.toAlgHom.toLinearMap
    rintro ⟨x, ⟨y, rfl⟩⟩
    exact ⟨y, rfl⟩
  · apply Completion.denseRange_coe.mono
    rintro _ ⟨z, rfl⟩
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk f z
    exact Set.mem_iUnion.mpr ⟨(completedEmbedding f i).range,
      Set.mem_iUnion.mpr ⟨⟨i, rfl⟩, ⟨x, rfl⟩⟩⟩

end NonCalkinAlgebra.NormedStarDirectLimit
