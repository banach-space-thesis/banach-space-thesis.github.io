import NonCalkinAlgebra.DenseMatrixSimplicity
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u v

/-- Approximately matricial means a directed dense union of unital full
matrix *-subalgebras. Sizes are written n+1 to include every positive size.
The indexing set is arbitrary and need not be countable. -/
def IsApproximatelyMatricial (A : Type u) [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A] : Prop :=
  ∃ S : Set (StarSubalgebra ℂ A), S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧
    (∀ B ∈ S, ∃ n : ℕ,
      Nonempty (B ≃⋆ₐ[ℂ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∧
    Dense (⋃ B ∈ S, (B : Set A))

variable {A : Type u} [CStarAlgebra A]

theorem matrixStarSubalgebra_finiteDimensional (B : StarSubalgebra ℂ A)
    (hB : ∃ n : ℕ, Nonempty (B ≃⋆ₐ[ℂ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) :
    FiniteDimensional ℂ B := by
  obtain ⟨n, ⟨e⟩⟩ := hB
  exact FiniteDimensional.of_injective e.toAlgEquiv.toLinearEquiv.toLinearMap e.injective

theorem matrixStarSubalgebra_isSimpleRing (B : StarSubalgebra ℂ A)
    (hB : ∃ n : ℕ, Nonempty (B ≃⋆ₐ[ℂ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) :
    IsSimpleRing B := by
  obtain ⟨n, ⟨e⟩⟩ := hB
  exact IsSimpleRing.of_ringEquiv e.symm.toAlgEquiv.toRingEquiv inferInstance

/-- AM implies AF with its actual directed finite-dimensional subalgebras. -/
theorem IsApproximatelyMatricial.isApproximatelyFiniteDimensional
    (h : IsApproximatelyMatricial A) : IsApproximatelyFiniteDimensional A := by
  obtain ⟨S, hne, hdir, hmat, hdense⟩ := h
  exact ⟨S, hne, hdir, fun B hB => matrixStarSubalgebra_finiteDimensional B (hmat B hB), hdense⟩

/-- Every nonzero unital AM C*-algebra is topologically simple as a Banach
algebra, including for closed ideals with no self-adjointness assumption. -/
theorem IsApproximatelyMatricial.isTopologicallySimple [Nontrivial A]
    (h : IsApproximatelyMatricial A) : IsTopologicallySimple A := by
  obtain ⟨S, _, _, hmat, hdense⟩ := h
  exact topologically_simple_of_dense_simple_finiteDimensional_starSubalgebras S
    (fun B hB => matrixStarSubalgebra_finiteDimensional B (hmat B hB))
    (fun B hB => matrixStarSubalgebra_isSimpleRing B (hmat B hB)) hdense

/-- AM abundance with Banach-algebra distinction suffices for the full AF
coefficient conclusion. The AM abundance/distinction are still inputs. -/
theorem AF_coefficient_existence_of_large_AM_family {J : Type}
    (D : J → ComplexCStarAlgebra.{0})
    (hlarge : Cardinal.continuum < Cardinal.mk J)
    (hdistinct : ∀ i j, Nonempty ((D i).Carrier ≃A[ℂ] (D j).Carrier) → i = j)
    (hAM : ∀ i, IsApproximatelyMatricial (D i).Carrier)
    (hdensity : ∀ i, HasDensityCharacter (D i).Carrier Cardinal.continuum) :
    AFCoefficientExistenceStatement.{v} := by
  exact AF_coefficient_existence_of_large_family D hlarge hdistinct
    (fun i => (hAM i).isApproximatelyFiniteDimensional) hdensity
    (fun i => (hAM i).isTopologicallySimple)

end NonCalkinAlgebra
