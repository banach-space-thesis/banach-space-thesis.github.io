import BanachIsometric.FiniteNerveRationalCoordinates

/-! The literal coefficient-sum augmentation of finite simplicial zero chains.
Its composition with the actual degree-one boundary is zero. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def finiteAugmentation (K : Complex ι) : FiniteRationalChains K 0 →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ (fun _ => LinearMap.id)

@[simp] theorem finiteAugmentation_single (K : Complex ι) (v : StrictOrderedSimplex K 0) (a : ℚ) :
    finiteAugmentation K (Finsupp.single v a) = a := Finsupp.lsum_single _ _ _ _

theorem finiteAugmentation_boundary (K : Complex ι) :
    (finiteAugmentation K).comp (finiteRationalBoundary K 0) = 0 := by
  apply Finsupp.lhom_ext
  intro v a
  have hsingle : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, finiteRationalBoundary_single, map_sum, map_zsmul,
    finiteAugmentation_single, LinearMap.zero_apply]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • (1 : ℚ)) = 0
  simp [Fin.sum_univ_two]

end BanachIsometric.FiniteNerve
