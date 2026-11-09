import PL1.KernelTranslations
import PL1.SingularConvolution
import PL1.SpikeSeparation
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-! # Independence of actual finite head and tail coordinates

The normalized Haar measure is identified with the unbiased infinite product.
Finite-coordinate functions on disjoint coordinate sets are therefore genuinely
independent for Haar and for every actual product-noise probability.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace PL1.HeadTail
open Walsh FiniteCoordinateKernels

/-- Dependence of a function on an actual finite set of coordinates. -/
def DependsOn {E : Type*} (S : Finset ℕ) (f : Walsh.Group → E) : Prop :=
  ∀ x y, (∀ j ∈ S, x j = y j) → f x = f y

theorem DependsOn.factor {E : Type*} {S : Finset ℕ} {f : Walsh.Group → E}
    (hf : DependsOn S f) (x : Walsh.Group) : f (FiniteCoordinateKernels.extend S (S.restrict x)) = f x :=
  hf _ _ (fun j hj => by simp [FiniteCoordinateKernels.extend, hj])

theorem DependsOn.continuous {E : Type*} [TopologicalSpace E]
    {S : Finset ℕ} {f : Walsh.Group → E} (hf : DependsOn S f) : Continuous f := by
  have he : f = (fun a : Assignments S => f (FiniteCoordinateKernels.extend S a)) ∘ S.restrict := by
    funext x
    exact (hf.factor x).symm
  rw [he]
  exact continuous_of_discreteTopology.comp (continuous_pi (fun j => continuous_apply (j : ℕ)))

theorem DependsOn.comp {E F : Type*} {S : Finset ℕ} {f : Walsh.Group → E}
    (hf : DependsOn S f) (g : E → F) : DependsOn S (g ∘ f) :=
  fun x y hxy => congrArg g (hf x y hxy)

theorem DependsOn.translate {E : Type*} {S : Finset ℕ} {f : Walsh.Group → E}
    (hf : DependsOn S f) (a : Walsh.Group) : DependsOn S (fun x => f (a * x)) :=
  fun _x _y hxy => hf _ _ (fun j hj => congrArg (fun z => a j * z) (hxy j hj))

def uniformCoordinate : Measure Sign :=
  bernoulliMeasure 1 (Multiplicative.ofAdd 1) ⟨1 / 2, by constructor <;> norm_num⟩

instance : IsProbabilityMeasure uniformCoordinate := by unfold uniformCoordinate; infer_instance

theorem integral_sign_uniform : ∫ a, signValue a ∂uniformCoordinate = 0 := by
  rw [uniformCoordinate, integral_bernoulliMeasure]
  norm_num [signValue]

/-- The Haar probability used throughout the project is the actual unbiased product. -/
theorem haar_eq_infinitePi : haar = Measure.infinitePi (fun _ : ℕ => uniformCoordinate) := by
  apply SingularConvolution.measure_eq_of_walsh_integrals
  intro F
  rw [Walsh.integral_character]
  have heq (x : Walsh.Group) : character F x = ∏ j : F, signValue (x j) :=
    (Finset.prod_coe_sort F (fun j => signValue (x j))).symm
  simp_rw [heq]
  change _ = ∫ x, (fun y : F → Sign => ∏ j, signValue (y j)) (F.restrict x)
    ∂Measure.infinitePi (fun _ : ℕ => uniformCoordinate)
  rw [integral_restrict_infinitePi (fun _ : ℕ => uniformCoordinate) (s := F) (f := fun y : F → Sign => ∏ j, signValue (y j))
    continuous_of_discreteTopology.aestronglyMeasurable, integral_fintype_prod_eq_prod]
  simp only [integral_sign_uniform]
  by_cases hF : F = ∅
  · subst F; simp
  · rw [ite_eq_right hF]
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    exact (Finset.prod_eq_zero (i := (⟨j, hj⟩ : F)) (Finset.mem_univ _) rfl).symm

theorem independent_restrictions (μ : ℕ → Measure Sign) [∀ j, IsProbabilityMeasure (μ j)]
    (S T : Finset ℕ) (hST : Disjoint S T) :
    IndepFun S.restrict T.restrict (Measure.infinitePi μ) :=
  (iIndepFun_infinitePi (P := μ) (X := fun _ a => a) (fun _ => measurable_id)).indepFun_finset
    S T hST (fun j => measurable_pi_apply j)

theorem indepFun {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : ℕ → Measure Sign) [∀ j, IsProbabilityMeasure (μ j)]
    {S T : Finset ℕ} {f : Walsh.Group → E} {g : Walsh.Group → F}
    (hST : Disjoint S T) (hf : DependsOn S f) (hg : DependsOn T g) :
    IndepFun f g (Measure.infinitePi μ) := by
  have h := (independent_restrictions μ S T hST).comp
    (measurable_of_finite (fun a : Assignments S => f (FiniteCoordinateKernels.extend S a)))
    (measurable_of_finite (fun a : Assignments T => g (FiniteCoordinateKernels.extend T a)))
  simpa only [Function.comp_def, hf.factor, hg.factor] using h

theorem indepFun_haar {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {S T : Finset ℕ} {f : Walsh.Group → E} {g : Walsh.Group → F}
    (hST : Disjoint S T) (hf : DependsOn S f) (hg : DependsOn T g) : IndepFun f g haar := by
  rw [haar_eq_infinitePi]
  exact indepFun _ hST hf hg

theorem indepFun_noise {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (rates : ℕ → ℝ≥0) (u : ℝ≥0) {S T : Finset ℕ}
    {f : Walsh.Group → E} {g : Walsh.Group → F}
    (hST : Disjoint S T) (hf : DependsOn S f) (hg : DependsOn T g) :
    IndepFun f g (Noise.measure rates u) := indepFun _ hST hf hg

end PL1.HeadTail

namespace PL1.HeadTail
open Walsh FiniteCoordinateKernels

/-- Arbitrary finite head/tail functions integrate as functions of independent copies. -/
theorem integral_headTail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Walsh.Group) [IsProbabilityMeasure μ] (S T : Finset ℕ)
    (hi : IndepFun S.restrict T.restrict μ) (F : Assignments S × Assignments T → E) :
    (∫ x, F (S.restrict x, T.restrict x) ∂μ) =
      ∫ x, ∫ y, F (S.restrict x, T.restrict y) ∂μ ∂μ := by
  have hS : Measurable (S.restrict : Walsh.Group → Assignments S) :=
    Measurable.of_eval (fun j => measurable_pi_apply (j : ℕ))
  have hT : Measurable (T.restrict : Walsh.Group → Assignments T) :=
    Measurable.of_eval (fun j => measurable_pi_apply (j : ℕ))
  have hF : Continuous F := continuous_of_discreteTopology
  have hm := hi.map_prod_eq_prod_map_map hS.aemeasurable hT.aemeasurable
  calc
    _ = ∫ z, F z ∂μ.map (fun x => (S.restrict x, T.restrict x)) :=
      (integral_map (hS.prodMk hT).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ z, F z ∂(μ.map S.restrict).prod (μ.map T.restrict) := by rw [hm]
    _ = ∫ a, ∫ b, F (a, b) ∂μ.map T.restrict ∂μ.map S.restrict :=
      integral_prod F (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    _ = ∫ x, ∫ b, F (S.restrict x, b) ∂μ.map T.restrict ∂μ :=
      integral_map hS.aemeasurable continuous_of_discreteTopology.aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => integral_map hT.aemeasurable
        continuous_of_discreteTopology.aestronglyMeasurable)

/-- A finite head/tail function separates under the project's actual Haar probability. -/
theorem integral_headTail_haar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S T : Finset ℕ) (hST : Disjoint S T) (F : Assignments S × Assignments T → E) :
    (∫ x, F (S.restrict x, T.restrict x) ∂haar) =
      ∫ x, ∫ y, F (S.restrict x, T.restrict y) ∂haar ∂haar := by
  apply integral_headTail
  rw [haar_eq_infinitePi]
  exact independent_restrictions _ S T hST

end PL1.HeadTail

namespace PL1.HeadTail
open Walsh FiniteCoordinateKernels

/-- Exact norm-product integration for functions on disjoint actual Haar coordinates. -/
theorem integral_norm_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S T : Finset ℕ} (hST : Disjoint S T)
    (f : C(Walsh.Group, E)) (q : C(Walsh.Group, ℝ))
    (hf : DependsOn S f) (hq : DependsOn T q) :
    (∫ x, ‖q x • f x‖ ∂haar) = (∫ x, ‖q x‖ ∂haar) * ∫ x, ‖f x‖ ∂haar := by
  simp only [norm_smul]
  exact (indepFun_haar hST.symm (hq.comp norm) (hf.comp norm)).integral_fun_mul_eq_mul_integral
    q.continuous.norm.aestronglyMeasurable f.continuous.norm.aestronglyMeasurable

/-- The concentration estimate on the original Haar space, with finite independent heads. -/
theorem concentration_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S T : Finset ℕ} (hST : Disjoint S T)
    (f g : C(Walsh.Group, E)) (q : C(Walsh.Group, ℝ))
    (hf : DependsOn S f) (hg : DependsOn S g) (hq : DependsOn T q)
    (hq0 : ∀ᵐ x ∂haar, 0 ≤ q x) (hq1 : ∫ x, q x ∂haar = 1)
    (B : Set Walsh.Group) (hB : MeasurableSet B) (δ : ℝ)
    (hsmall : haar.real B ≤ δ) (hconcentrated : 1 - δ ≤ ∫ x in B, q x ∂haar) :
    (1 - 2 * δ) * ((∫ x, ‖f x‖ ∂haar) + ∫ x, ‖g x‖ ∂haar) ≤
      ∫ x, ‖f x + q x • g x‖ ∂haar := by
  have he := integral_headTail_haar S T hST (fun z : Assignments S × Assignments T =>
    ‖f (FiniteCoordinateKernels.extend S z.1) +
      q (FiniteCoordinateKernels.extend T z.2) • g (FiniteCoordinateKernels.extend S z.1)‖)
  simp only [hf.factor, hg.factor, hq.factor] at he
  rw [he]
  have hiq : Integrable (q : Walsh.Group → ℝ) haar :=
    q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hif : Integrable (fun x => ‖f x‖) haar :=
    f.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hig : Integrable (fun x => ‖g x‖) haar :=
    g.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiraw : DependsOn S (fun x => ∫ y, ‖f x + q y • g x‖ ∂haar) := by
    intro x z hxz
    simp only [hf x z hxz, hg x z hxz]
  have hi : Integrable (fun x => ∫ y, ‖f x + q y • g x‖ ∂haar) haar := hiraw.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono ((hif.add hig).const_mul (1 - 2 * δ)) hi (fun x =>
    SpikeSeparation.concentration_lower_bound hiq hq0 hq1 B hB δ hsmall hconcentrated (f x) (g x))
  simpa only [integral_const_mul, Pi.add_apply, integral_add hif hig] using h

#print axioms concentration_lower_bound
end PL1.HeadTail
