import BanachIsometric.VectorChainHomotopy
import BanachIsometric.VectorChainNormalizedContraction

/-! The homology projection has an actual contractible kernel complex.
Every degree is linearly the product of actual homology and that kernel. -/

noncomputable section
universe u
namespace BanachIsometric.VectorChainSplitting
open CategoryTheory

variable {K : Type*} [Field K] (C : ℕ → ModuleCat.{u} K)
  (d : ∀ n, C (n + 1) →ₗ[K] C n)
  (hd : ∀ n, (d n).comp (d (n + 1)) = 0)

abbrev homologyKernel (n : ℕ) := LinearMap.ker (homologyProjection C d hd n)

def kernelProjection (n : ℕ) : C n →ₗ[K] homologyKernel C d hd n :=
  (LinearMap.id - (homologyInclusion C d hd n).comp (homologyProjection C d hd n)).codRestrict
    (homologyKernel C d hd n) (by
      intro x
      change homologyProjection C d hd n
        (x - homologyInclusion C d hd n (homologyProjection C d hd n x)) = 0
      rw [map_sub, homologyProjection_inclusion]
      exact sub_self _)

def degreeSplit (n : ℕ) : C n ≃ₗ[K] Homology C d hd n × homologyKernel C d hd n where
  toFun x := (homologyProjection C d hd n x, kernelProjection C d hd n x)
  invFun a := homologyInclusion C d hd n a.1 + a.2.val
  left_inv x := by
    change homologyInclusion C d hd n (homologyProjection C d hd n x) +
      (x - homologyInclusion C d hd n (homologyProjection C d hd n x)) = x
    abel
  right_inv a := by
    apply Prod.ext
    · change homologyProjection C d hd n (homologyInclusion C d hd n a.1 + a.2.val) = a.1
      rw [map_add, homologyProjection_inclusion, a.2.property, add_zero]
    · apply Subtype.ext
      change homologyInclusion C d hd n a.1 + a.2.val - homologyInclusion C d hd n
        (homologyProjection C d hd n (homologyInclusion C d hd n a.1 + a.2.val)) = a.2.val
      rw [map_add, homologyProjection_inclusion, a.2.property, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · exact map_add _ _ _
  map_smul' r x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · exact map_smul _ _ _

def kernelDifferential (n : ℕ) :
    homologyKernel C d hd (n + 1) →ₗ[K] homologyKernel C d hd n :=
  ((d n).domRestrict (homologyKernel C d hd (n + 1))).codRestrict
    (homologyKernel C d hd n) (fun x => homologyProjection_boundary C d hd n x.val)

theorem kernelDifferential_squared (n : ℕ) :
    (kernelDifferential C d hd n).comp (kernelDifferential C d hd (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (hd n) x.val

def kernelContraction (n : ℕ) :
    homologyKernel C d hd n →ₗ[K] homologyKernel C d hd (n + 1) :=
  ((contraction C d hd n).domRestrict (homologyKernel C d hd n)).codRestrict
    (homologyKernel C d hd (n + 1)) (fun x => homologyProjection_contraction C d hd n x.val)

abbrev kernelChainComplex : ChainComplex (ModuleCat.{u} K) ℕ :=
  chainComplex (fun n => ModuleCat.of K (homologyKernel C d hd n))
    (kernelDifferential C d hd) (kernelDifferential_squared C d hd)

def kernelContractibleHomotopy : Homotopy (𝟙 (kernelChainComplex C d hd)) 0 :=
  chainHomotopyOfDegreeOne (fun n => ModuleCat.ofHom (kernelContraction C d hd n)) (by
    rw [chainComplex_d]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change x.val = d 0 (contraction C d hd 0 x.val) + 0
    have h := contraction_zero_identity C d hd x.val
    rw [x.property, map_zero, sub_zero] at h
    simpa only [add_zero] using h.symm) (by
      intro n
      rw [chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext_iff.mpr
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change x.val = contraction C d hd n (d n x.val) +
        d (n + 1) (contraction C d hd (n + 1) x.val) + 0
      have h := contraction_succ_identity C d hd n x.val
      rw [x.property, map_zero, sub_zero] at h
      calc
        x.val = d (n + 1) (contraction C d hd (n + 1) x.val) +
            contraction C d hd n (d n x.val) := h.symm
        _ = _ := by abel)

end BanachIsometric.VectorChainSplitting
