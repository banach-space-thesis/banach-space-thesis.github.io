import BanachIsometric.EilenbergZilberProductComposite

/-! Every product singular simplex is the pushforward of the diagonal
simplex in the product of its actual two simplex domains. This supplies the
natural extension from each fixed universal homotopy chain. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

def universalProductDiagonal (n : ℕ) : RawSingularSimplex (Simplex n × Simplex n) n :=
  ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩

def universalProductGenerator (n : ℕ) : RawRationalChains (Simplex n × Simplex n) n :=
  Finsupp.single (universalProductDiagonal n) 1

def productSimplexFst {n : ℕ} (σ : RawSingularSimplex (X × Y) n) : C(Simplex n, X) :=
  ⟨fun x => (σ x).1, continuous_fst.comp σ.continuous⟩

def productSimplexSnd {n : ℕ} (σ : RawSingularSimplex (X × Y) n) : C(Simplex n, Y) :=
  ⟨fun x => (σ x).2, continuous_snd.comp σ.continuous⟩

theorem universalProductGenerator_pushforward {n : ℕ} (σ : RawSingularSimplex (X × Y) n) :
    rawChainMap (awProductMap (productSimplexFst σ) (productSimplexSnd σ)) n
      (universalProductGenerator n) = Finsupp.single σ 1 := by
  have h : (awProductMap (productSimplexFst σ) (productSimplexSnd σ)).comp
      (universalProductDiagonal n) = σ := by
    apply ContinuousMap.ext
    intro x
    rfl
  simp only [universalProductGenerator, rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, h]

def universalProductHomotopyEvaluation {n : ℕ}
    (K : RawRationalChains (Simplex n × Simplex n) (n + 1)) :
    RawRationalChains (X × Y) n →ₗ[ℚ] RawRationalChains (X × Y) (n + 1) :=
  Finsupp.linearCombination ℚ (fun σ =>
    rawChainMap (awProductMap (productSimplexFst σ) (productSimplexSnd σ)) (n + 1) K)

theorem universalProductHomotopyEvaluation_generator {n : ℕ}
    (K : RawRationalChains (Simplex n × Simplex n) (n + 1)) :
    universalProductHomotopyEvaluation K (universalProductGenerator n) = K := by
  simp only [universalProductHomotopyEvaluation, universalProductGenerator,
    Finsupp.linearCombination_single, one_smul]
  change rawChainMap (ContinuousMap.id (Simplex n × Simplex n)) (n + 1) K = K
  rw [rawChainMap_id, LinearMap.id_apply]

theorem universalProductHomotopyEvaluation_naturality {n : ℕ}
    (K : RawRationalChains (Simplex n × Simplex n) (n + 1))
    (f : C(X, X')) (g : C(Y, Y')) (c : RawRationalChains (X × Y) n) :
    universalProductHomotopyEvaluation K (rawChainMap (awProductMap f g) n c) =
      rawChainMap (awProductMap f g) (n + 1) (universalProductHomotopyEvaluation K c) := by
  have h :
      (universalProductHomotopyEvaluation K).comp (rawChainMap (awProductMap f g) n) =
        (rawChainMap (awProductMap f g) (n + 1)).comp (universalProductHomotopyEvaluation K) := by
    apply Finsupp.lhom_ext
    intro σ a
    change universalProductHomotopyEvaluation K (rawChainMap (awProductMap f g) n (Finsupp.single σ a)) =
      rawChainMap (awProductMap f g) (n + 1) (universalProductHomotopyEvaluation K (Finsupp.single σ a))
    have hsingle : rawChainMap (awProductMap f g) n (Finsupp.single σ a) =
      Finsupp.single ((awProductMap f g).comp σ) a := by simp [rawChainMap]
    rw [hsingle]
    simp only [universalProductHomotopyEvaluation, Finsupp.linearCombination_single, map_smul]
    have hprod : (awProductMap f g).comp
        (awProductMap (productSimplexFst σ) (productSimplexSnd σ)) =
          awProductMap (productSimplexFst ((awProductMap f g).comp σ))
            (productSimplexSnd ((awProductMap f g).comp σ)) := rfl
    have hpush := LinearMap.congr_fun
      (rawChainMap_comp (awProductMap (productSimplexFst σ) (productSimplexSnd σ))
        (awProductMap f g) (n + 1)) K
    rw [hprod] at hpush
    exact congrArg (fun x => a • x) hpush
  exact LinearMap.congr_fun h c

end BanachIsometric.SingularEZ
