import BanachIsometric.SubdivisionAffineCompatibility
import BanachIsometric.AffineSubdivisionIteration
import BanachIsometric.UniversalSubdivisionBoundary

/-! Literal powers of singular subdivision are represented by powers of
the actual affine subdivision on the universal simplex. This gives a
concrete geometric model for every iterate. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

theorem linearMap_power_intertwines {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (A : U →ₗ[ℚ] U) (B : V →ₗ[ℚ] V) (f : U →ₗ[ℚ] V)
    (h : B.comp f = f.comp A) (k : ℕ) : (B ^ k).comp f = f.comp (A ^ k) := by
  induction k with
  | zero =>
    change LinearMap.id.comp f = f.comp LinearMap.id
    rw [LinearMap.id_comp, LinearMap.comp_id]
  | succ k ih =>
    apply LinearMap.ext
    intro c
    have hih := LinearMap.congr_fun ih c
    have hp := LinearMap.congr_fun h ((A ^ k) c)
    simp only [LinearMap.comp_apply] at hih hp
    change (B ^ (k + 1)) (f c) = f ((A ^ (k + 1)) c)
    simp only [pow_succ', Module.End.mul_apply]
    rw [hih, hp]

theorem affineSubdivision_carrier_power {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) (n k : ℕ) :
    affineCarrier s n ≤ (affineCarrier s n).comap (affineSubdivision n ^ k) := by
  induction k with
  | zero => exact fun _ hc => hc
  | succ k ih =>
    intro c hc
    have h := affineSubdivision_carrier hs n (ih hc)
    simpa only [pow_succ', Module.End.mul_apply] using h

def universalAffineSubdivisionPower (n k : ℕ) : affineCarrier (stdSimplex ℝ (Fin (n + 1))) n :=
  ⟨(affineSubdivision n ^ k) (universalAffineSimplex n).val,
    affineSubdivision_carrier_power (convex_stdSimplex ℝ _) n k (universalAffineSimplex n).property⟩

def universalSingularSubdivisionPower (n k : ℕ) : RawRationalChains (Simplex n) n :=
  affineCarrierRealization (convex_stdSimplex ℝ _) n (universalAffineSubdivisionPower n k)

theorem universalSingularSubdivisionPower_ambient (n k : ℕ) :
    rawChainMap (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 1)))) n
        (universalSingularSubdivisionPower n k) =
      affineChainRealization n ((affineSubdivision n ^ k)
        (Finsupp.single (simplexStandardVertices n) 1)) :=
  affineCarrierRealization_ambient_apply (convex_stdSimplex ℝ _) n (universalAffineSubdivisionPower n k)

theorem rawSubdivision_power_universal (n k : ℕ) :
    (rawSubdivision (Simplex n) n ^ k) (Finsupp.single (ContinuousMap.id (Simplex n)) 1) =
      universalSingularSubdivisionPower n k := by
  let incl := affineCarrierInclusion (stdSimplex ℝ (Fin (n + 1)))
  apply rawChainMap_injective incl Subtype.val_injective n
  have hn := linearMap_power_intertwines (rawSubdivision (Simplex n) n)
    (rawSubdivision (Fin (n + 1) → ℝ) n) (rawChainMap incl n) (rawSubdivision_natural incl n) k
  have ha := linearMap_power_intertwines (affineSubdivision n)
    (rawSubdivision (Fin (n + 1) → ℝ) n) (affineChainRealization n)
      (rawSubdivision_affineChainRealization n) k
  have hnp := LinearMap.congr_fun hn (Finsupp.single (ContinuousMap.id (Simplex n)) 1)
  have hap := LinearMap.congr_fun ha (Finsupp.single (simplexStandardVertices n) 1)
  simp only [LinearMap.comp_apply] at hnp hap
  calc
    _ = (rawSubdivision (Fin (n + 1) → ℝ) n ^ k)
        (rawChainMap incl n (Finsupp.single (ContinuousMap.id (Simplex n)) 1)) := hnp.symm
    _ = (rawSubdivision (Fin (n + 1) → ℝ) n ^ k)
        (affineChainRealization n (Finsupp.single (simplexStandardVertices n) 1)) := by
      rw [universalIdentity_ambient]
    _ = affineChainRealization n ((affineSubdivision n ^ k)
        (Finsupp.single (simplexStandardVertices n) 1)) := hap
    _ = _ := (universalSingularSubdivisionPower_ambient n k).symm

theorem rawSubdivision_power_single {X : Type*} [TopologicalSpace X]
    (n k : ℕ) (simplex : RawSingularSimplex X n) :
    (rawSubdivision X n ^ k) (Finsupp.single simplex 1) =
      rawChainMap simplex n (universalSingularSubdivisionPower n k) := by
  have h := LinearMap.congr_fun
    (linearMap_power_intertwines (rawSubdivision (Simplex n) n) (rawSubdivision X n)
      (rawChainMap simplex n) (rawSubdivision_natural simplex n) k)
    (Finsupp.single (ContinuousMap.id (Simplex n)) 1)
  simp only [LinearMap.comp_apply, rawChainMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, ContinuousMap.comp_id] at h
  rw [h, rawSubdivision_power_universal]
  rfl

end BanachIsometric.SingularPrism
