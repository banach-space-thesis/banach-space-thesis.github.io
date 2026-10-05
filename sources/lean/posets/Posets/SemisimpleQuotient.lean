import Posets.SemisimpleQuotientTools
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Finite-dimensional complex semisimple quotients, assuming Theorem 1.5. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

abbrev fullOperatorFactor (m : ℕ) := (Fin m → 𝕜) →L[𝕜] (Fin m → 𝕜)

theorem admissible_fullOperatorFactor (m : ℕ) : AdmissibleAlgebra 𝕜 (fullOperatorFactor 𝕜 m) := by
  cases m with
  | zero => exact Or.inl inferInstance
  | succ m =>
    refine Or.inr (Or.inl ⟨m, ?_⟩)
    let f : BoundedHom 𝕜 (fullOperatorFactor 𝕜 (m + 1)) (fullOperatorFactor 𝕜 (m + 1)) :=
      ⟨ContinuousLinearMap.id 𝕜 _, fun _ _ => rfl⟩
    refine ⟨f, isometry_id, ?_⟩
    ext T
    exact ⟨fun _ => Set.mem_univ _, fun _ => ⟨T, rfl⟩⟩

def fullOperatorMatrixAlgEquiv (m : ℕ) :
    fullOperatorFactor 𝕜 m ≃ₐ[𝕜] Matrix (Fin m) (Fin m) 𝕜 :=
  (Module.End.toContinuousLinearMap (𝕜 := 𝕜) (Fin m → 𝕜)).symm.trans
    LinearMap.toMatrixAlgEquiv'

def paddedMatrixSize (n : ℕ) (d : Fin n → ℕ) (m : ℕ) : ℕ :=
  if h : m < n then d ⟨m, h⟩ else 0

abbrev paddedFullOperatorFactor (n : ℕ) (d : Fin n → ℕ) (m : ℕ) :=
  fullOperatorFactor 𝕜 (paddedMatrixSize n d m)

theorem paddedFullOperatorFactor_trivial_tail (n : ℕ) (d : Fin n → ℕ)
    (m : ℕ) (hm : n ≤ m) : Subsingleton (paddedFullOperatorFactor 𝕜 n d m) := by
  simp only [paddedFullOperatorFactor, paddedMatrixSize, dif_neg (not_lt.mpr hm)]
  infer_instance

def paddedFullOperatorMatrixAlgEquiv (n : ℕ) (d : Fin n → ℕ) (i : Fin n) :
    paddedFullOperatorFactor 𝕜 n d i.val ≃ₐ[𝕜] Matrix (Fin (d i)) (Fin (d i)) 𝕜 := by
  change fullOperatorFactor 𝕜 (paddedMatrixSize n d i.val) ≃ₐ[𝕜] Matrix (Fin (d i)) (Fin (d i)) 𝕜
  have hs : paddedMatrixSize n d i.val = d i := dif_pos i.isLt
  rw [hs]
  exact fullOperatorMatrixAlgEquiv 𝕜 (d i)

/-- The finite-dimensional semisimple case is an actual algebra equivalence
of the normed separable-range quotient. Only Theorem 1.5 remains as input. -/
theorem exists_semisimple_quotient_algEquiv_of_theorem_1_5
    (hquot : ∀ (D : ℕ → Type) [∀ m, NormedRing (D m)] [∀ m, NormedAlgebra ℂ (D m)]
      [∀ m, CompleteSpace (D m)], Theorem_1_5 ℂ D)
    (C : Type) [Ring C] [Algebra ℂ C] [FiniteDimensional ℂ C] [IsSemisimpleRing C] :
    ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
      Nonempty (SeparableQuotient ℂ (Space ℂ 𝒜) ≃ₐ[ℂ] C) := by
  obtain ⟨n, d, _, ⟨eC⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ C
  let D := paddedFullOperatorFactor ℂ n d
  have hD (m : ℕ) : AdmissibleAlgebra ℂ (D m) := admissible_fullOperatorFactor ℂ _
  obtain ⟨𝒜, hAD, θ, ρ, hs, _, _⟩ := hquot D hD
  let e₀ := strongSplitQuotientLinearEquiv θ ρ hs
  let e₁ := normedProductPrefixLinearEquiv (𝕜 := ℂ) D n
    (paddedFullOperatorFactor_trivial_tail ℂ n d)
  let e₂ : (Π i : Fin n, D i.val) ≃ₐ[ℂ] (Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
    AlgEquiv.piCongrRight (paddedFullOperatorMatrixAlgEquiv ℂ n d)
  let e := ((e₀.trans e₁).trans e₂.toLinearEquiv).trans eC.symm.toLinearEquiv
  have hmul (S T : Space ℂ 𝒜 →L[ℂ] Space ℂ 𝒜) :
      e (quotientMap ℂ (Space ℂ 𝒜) (S * T)) =
        e (quotientMap ℂ (Space ℂ 𝒜) S) * e (quotientMap ℂ (Space ℂ 𝒜) T) := by
    change eC.symm (e₂ (e₁ (θ (S * T)))) = eC.symm (e₂ (e₁ (θ S))) * eC.symm (e₂ (e₁ (θ T)))
    rw [θ.map_mul', normedProductPrefixLinearEquiv_map_mul]
    simp only [map_mul]
    rfl
  exact ⟨𝒜, hAD, ⟨quotientAlgEquivOfRepresentatives e hmul⟩⟩

theorem corollary_1_7_of_theorem_1_5
    (hquot : ∀ (D : ℕ → Type) [∀ m, NormedRing (D m)] [∀ m, NormedAlgebra ℂ (D m)]
      [∀ m, CompleteSpace (D m)], Theorem_1_5 ℂ D)
    (C : Type) [Ring C] [Algebra ℂ C] [FiniteDimensional ℂ C] [IsSemisimpleRing C] :
    Corollary_1_7 C := by
  obtain ⟨𝒜, hAD, ⟨e⟩⟩ := exists_semisimple_quotient_algEquiv_of_theorem_1_5 hquot C
  refine ⟨𝒜, hAD, e.toLinearEquiv, ?_⟩
  intro S T
  exact e.map_mul (quotientMap ℂ (Space ℂ 𝒜) S) (quotientMap ℂ (Space ℂ 𝒜) T)

end Posets
