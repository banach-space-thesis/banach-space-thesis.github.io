import BanachIsometric.EilenbergZilberProductEvaluation

/-! A homotopy equation on the literal diagonal model simplex extends to
all product singular chains by strict naturality. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def productModelDifference (n : ℕ) : RawRationalChains (Simplex n × Simplex n) n :=
  rawProductComposite n (universalProductGenerator n) - universalProductGenerator n

def productModelHomotopyCandidate {n : ℕ}
    (K : RawRationalChains (Simplex n × Simplex n) (n + 1)) :
    RawRationalChains (Simplex (n + 1) × Simplex (n + 1)) (n + 1) :=
  productModelDifference (n + 1) -
    universalProductHomotopyEvaluation K (rawBoundary n (universalProductGenerator (n + 1)))

theorem productHomotopy_zero_of_model
    {K : RawRationalChains (Simplex 0 × Simplex 0) 1}
    (hK : rawBoundary 0 K = productModelDifference 0) (c : RawRationalChains (X × Y) 0) :
    rawBoundary 0 (universalProductHomotopyEvaluation K c) = rawProductComposite 0 c - c := by
  have h : (rawBoundary (X := X × Y) 0).comp (universalProductHomotopyEvaluation K) =
      rawProductComposite 0 - LinearMap.id := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    change rawBoundary 0 (universalProductHomotopyEvaluation K (Finsupp.single σ 1)) =
      rawProductComposite 0 (Finsupp.single σ 1) - Finsupp.single σ 1
    let f := productSimplexFst σ
    let g := productSimplexSnd σ
    let F := awProductMap f g
    have hgen : rawChainMap F 0 (universalProductGenerator 0) = Finsupp.single σ 1 :=
      universalProductGenerator_pushforward σ
    rw [← hgen, universalProductHomotopyEvaluation_naturality,
      universalProductHomotopyEvaluation_generator, rawProductComposite_naturality, ← map_sub]
    exact (LinearMap.congr_fun (rawChainMap_boundary F 0) K).trans (congrArg (rawChainMap F 0) hK)
  exact LinearMap.congr_fun h c

theorem productHomotopy_succ_of_model {n : ℕ}
    {K : RawRationalChains (Simplex n × Simplex n) (n + 1)}
    {L : RawRationalChains (Simplex (n + 1) × Simplex (n + 1)) ((n + 1) + 1)}
    (hL : rawBoundary (n + 1) L = productModelHomotopyCandidate K)
    (c : RawRationalChains (X × Y) (n + 1)) :
    rawBoundary (n + 1) (universalProductHomotopyEvaluation L c) =
      rawProductComposite (n + 1) c - c - universalProductHomotopyEvaluation K (rawBoundary n c) := by
  have h : (rawBoundary (X := X × Y) (n + 1)).comp (universalProductHomotopyEvaluation L) =
      rawProductComposite (n + 1) - LinearMap.id -
        (universalProductHomotopyEvaluation K).comp (rawBoundary n) := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    change rawBoundary (n + 1) (universalProductHomotopyEvaluation L (Finsupp.single σ 1)) =
      rawProductComposite (n + 1) (Finsupp.single σ 1) - Finsupp.single σ 1 -
        universalProductHomotopyEvaluation K (rawBoundary n (Finsupp.single σ 1))
    let f := productSimplexFst σ
    let g := productSimplexSnd σ
    let F := awProductMap f g
    have hgen : rawChainMap F (n + 1) (universalProductGenerator (n + 1)) = Finsupp.single σ 1 :=
      universalProductGenerator_pushforward σ
    have hb := LinearMap.congr_fun (rawChainMap_boundary F n) (universalProductGenerator (n + 1))
    simp only [LinearMap.comp_apply] at hb
    rw [← hgen, universalProductHomotopyEvaluation_naturality,
      universalProductHomotopyEvaluation_generator, rawProductComposite_naturality, hb,
      universalProductHomotopyEvaluation_naturality, ← map_sub, ← map_sub]
    exact (LinearMap.congr_fun (rawChainMap_boundary F (n + 1)) L).trans
      (congrArg (rawChainMap F (n + 1)) hL)
  exact LinearMap.congr_fun h c

end BanachIsometric.SingularEZ
