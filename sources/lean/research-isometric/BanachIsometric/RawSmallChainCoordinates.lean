import BanachIsometric.RawSmallChains

/-! Literal free rational coordinates for the shared actual small-chain
submodule. Face precomposition preserves smallness. The boundary is the
actual alternating face sum, commutes with inclusion into raw singular
chains, and squares to zero by the injective actual chain inclusion. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)

abbrev RawSmallSimplex (n : ℕ) :=
  {σ : RawSingularSimplex X n // ∃ i, Set.range σ ⊆ U i}

abbrev RawSmallCoordinates (n : ℕ) := RawSmallSimplex U n →₀ ℚ

def rawSmallCoordinateEquiv (n : ℕ) :
    rawSmallChainCarrier U n ≃ₗ[ℚ] RawSmallCoordinates U n :=
  Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ) _

def rawSmallCoordinateInclusion (n : ℕ) :
    RawSmallCoordinates U n →ₗ[ℚ] RawRationalChains X n :=
  Finsupp.lmapDomain ℚ ℚ (fun σ : RawSmallSimplex U n => σ.val)

@[simp] theorem rawSmallCoordinateInclusion_single (n : ℕ) (σ : RawSmallSimplex U n) (a : ℚ) :
    rawSmallCoordinateInclusion U n (Finsupp.single σ a) = Finsupp.single σ.val a :=
  Finsupp.mapDomain_single

theorem rawSmallCoordinateInclusion_injective (n : ℕ) :
    Function.Injective (rawSmallCoordinateInclusion U n) :=
  Finsupp.mapDomain_injective (fun _ _ h => Subtype.ext h)

theorem rawSmallCoordinateEquiv_symm_coe (n : ℕ) (c : RawSmallCoordinates U n) :
    ((rawSmallCoordinateEquiv U n).symm c : RawRationalChains X n) =
      rawSmallCoordinateInclusion U n c := by
  have h : (rawSmallChainCarrier U n).subtype.comp (rawSmallCoordinateEquiv U n).symm.toLinearMap =
      rawSmallCoordinateInclusion U n := by
    apply Finsupp.lhom_ext
    intro σ a
    change ((rawSmallCoordinateEquiv U n).symm (Finsupp.single σ a) : RawRationalChains X n) =
      rawSmallCoordinateInclusion U n (Finsupp.single σ a)
    rw [rawSmallCoordinateInclusion_single]
    exact Finsupp.supportedEquivFinsupp_symm_single (M := ℚ) (R := ℚ) _ σ a
  exact LinearMap.congr_fun h c

theorem rawSmallCoordinateInclusion_mem (n : ℕ) (c : RawSmallCoordinates U n) :
    rawSmallCoordinateInclusion U n c ∈ rawSmallChainCarrier U n := by
  rw [← rawSmallCoordinateEquiv_symm_coe]
  exact ((rawSmallCoordinateEquiv U n).symm c).property

def rawSmallCoordinateFace {n : ℕ} (i : Fin (n + 2)) (σ : RawSmallSimplex U (n + 1)) :
    RawSmallSimplex U n := by
  refine ⟨σ.val.comp (face i), ?_⟩
  obtain ⟨j, hj⟩ := σ.property
  refine ⟨j, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hj (Set.mem_range_self (face i z))

def rawSmallCoordinateBoundary (n : ℕ) :
    RawSmallCoordinates U (n + 1) →ₗ[ℚ] RawSmallCoordinates U n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.lmapDomain ℚ ℚ (rawSmallCoordinateFace U i)

theorem rawSmallCoordinateBoundary_single (n : ℕ) (σ : RawSmallSimplex U (n + 1)) (a : ℚ) :
    rawSmallCoordinateBoundary U n (Finsupp.single σ a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (rawSmallCoordinateFace U i σ) a := by
  simp only [rawSmallCoordinateBoundary, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem rawSmallCoordinateInclusion_boundary (n : ℕ) :
    (rawBoundary (X := X) n).comp (rawSmallCoordinateInclusion U (n + 1)) =
      (rawSmallCoordinateInclusion U n).comp (rawSmallCoordinateBoundary U n) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply, rawSmallCoordinateInclusion_single,
    rawSmallCoordinateBoundary_single, rawBoundary_single, map_sum, map_zsmul]
  rfl

theorem rawSmallCoordinateBoundary_squared (n : ℕ) :
    (rawSmallCoordinateBoundary U n).comp (rawSmallCoordinateBoundary U (n + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply rawSmallCoordinateInclusion_injective U n
  have h₁ := LinearMap.congr_fun (rawSmallCoordinateInclusion_boundary U n)
    (rawSmallCoordinateBoundary U (n + 1) c)
  have h₂ := LinearMap.congr_fun (rawSmallCoordinateInclusion_boundary U (n + 1)) c
  change rawBoundary n (rawSmallCoordinateInclusion U (n + 1)
    (rawSmallCoordinateBoundary U (n + 1) c)) =
      rawSmallCoordinateInclusion U n (rawSmallCoordinateBoundary U n
        (rawSmallCoordinateBoundary U (n + 1) c)) at h₁
  change rawBoundary (n + 1) (rawSmallCoordinateInclusion U (n + 2) c) =
    rawSmallCoordinateInclusion U (n + 1) (rawSmallCoordinateBoundary U (n + 1) c) at h₂
  change rawSmallCoordinateInclusion U n (rawSmallCoordinateBoundary U n
    (rawSmallCoordinateBoundary U (n + 1) c)) = rawSmallCoordinateInclusion U n 0
  rw [← h₁, ← h₂, map_zero]
  exact LinearMap.congr_fun (rawBoundary_squared n) _

def rawSmallCoordinateAugmentation : RawSmallCoordinates U 0 →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ (fun _ => LinearMap.id)

@[simp] theorem rawSmallCoordinateAugmentation_single (σ : RawSmallSimplex U 0) (a : ℚ) :
    rawSmallCoordinateAugmentation U (Finsupp.single σ a) = a := Finsupp.lsum_single _ _ _ _

theorem rawSmallCoordinateAugmentation_boundary :
    (rawSmallCoordinateAugmentation U).comp (rawSmallCoordinateBoundary U 0) = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply, rawSmallCoordinateBoundary_single, map_sum, map_zsmul,
    rawSmallCoordinateAugmentation_single, LinearMap.zero_apply]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • a) = 0
  simp [Fin.sum_univ_two]

end BanachIsometric.SingularPrism
