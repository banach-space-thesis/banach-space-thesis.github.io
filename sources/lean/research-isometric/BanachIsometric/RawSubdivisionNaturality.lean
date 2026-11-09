import BanachIsometric.UniversalSingularSubdivision
import BanachIsometric.RawSingularHomology

/-! The literal universal-chain construction of subdivision and its
homotopy is natural under every actual continuous target map. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem rawSubdivision_natural (f : C(X, Y)) (n : ℕ) :
    (rawSubdivision Y n).comp (rawChainMap f n) =
      (rawChainMap f n).comp (rawSubdivision X n) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have ha : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  change rawSubdivision Y n (rawChainMap f n (Finsupp.single simplex 1)) =
    rawChainMap f n (rawSubdivision X n (Finsupp.single simplex 1))
  simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [rawSubdivision_single_one, rawSubdivision_single_one]
  exact LinearMap.congr_fun (rawChainMap_comp simplex f n) (universalSingularSubdivision n)

theorem rawSubdivisionHomotopy_natural (f : C(X, Y)) (n : ℕ) :
    (rawSubdivisionHomotopy Y n).comp (rawChainMap f n) =
      (rawChainMap f (n + 1)).comp (rawSubdivisionHomotopy X n) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have ha : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  change rawSubdivisionHomotopy Y n (rawChainMap f n (Finsupp.single simplex 1)) =
    rawChainMap f (n + 1) (rawSubdivisionHomotopy X n (Finsupp.single simplex 1))
  simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [rawSubdivisionHomotopy_single_one, rawSubdivisionHomotopy_single_one]
  exact LinearMap.congr_fun (rawChainMap_comp simplex f (n + 1))
    (universalSingularSubdivisionHomotopy n)

end BanachIsometric.SingularPrism
