import BanachIsometric.RawSingularHomotopyInvariance

/-! Positive singular homology of an actual one-point space vanishes.
The proof computes the literal alternating constant-simplex differential;
no homology normalization axiom is introduced. Constant maps therefore act
as zero in every positive degree. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem rawBoundary_const_single (n : ℕ) (x : X) (a : ℚ) :
    rawBoundary n (Finsupp.single (ContinuousMap.const (Simplex (n + 1)) x) a) =
      (if Even (n + 2) then (0 : ℤ) else 1) •
        Finsupp.single (ContinuousMap.const (Simplex n) x) a := by
  rw [rawBoundary_single]
  have hc (i : Fin (n + 2)) :
      (ContinuousMap.const (Simplex (n + 1)) x).comp (face i) =
        ContinuousMap.const (Simplex n) x := by
    ext w
    rfl
  simp only [hc, ← Finset.sum_smul, Fin.sum_neg_one_pow]

theorem rawChain_subsingleton_single [Subsingleton X] (n : ℕ) (x : X)
    (c : RawRationalChains X n) :
    c = Finsupp.single (ContinuousMap.const (Simplex n) x)
      (c (ContinuousMap.const (Simplex n) x)) := by
  classical
  ext σ
  have hσ : σ = ContinuousMap.const (Simplex n) x := Subsingleton.elim _ _
  subst σ
  simp

theorem rawCycles_subsingleton_mem_boundaries [Subsingleton X] (n : ℕ) (x : X)
    (c : rawCycles X n) : c ∈ rawBoundaries X n := by
  let a := c.val (ContinuousMap.const (Simplex (n + 1)) x)
  have hc : c.val = Finsupp.single (ContinuousMap.const (Simplex (n + 1)) x) a :=
    rawChain_subsingleton_single (n + 1) x c.val
  by_cases he : Even (n + 2)
  · have hne : ¬ Even (n + 1 + 2) := by
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.even_add_one]
      exact not_not.mpr he
    refine ⟨Finsupp.single (ContinuousMap.const (Simplex (n + 2)) x) a, ?_⟩
    apply Subtype.ext
    change rawBoundary (n + 1)
      (Finsupp.single (ContinuousMap.const (Simplex (n + 2)) x) a) = c.val
    rw [rawBoundary_const_single, if_neg hne, one_smul]
    exact hc.symm
  · have hz := c.property
    change rawBoundary n c.val = 0 at hz
    rw [hc, rawBoundary_const_single, if_neg he, one_smul] at hz
    have ha : a = 0 := by
      simpa using congrArg (fun d : RawRationalChains X n =>
        d (ContinuousMap.const (Simplex n) x)) hz
    have hcz : c = 0 := by
      apply Subtype.ext
      simp only [hc, ha, Finsupp.single_zero, ZeroMemClass.coe_zero]
    rw [hcz]
    exact (rawBoundaries X n).zero_mem

theorem rawPositiveHomology_subsingleton [Subsingleton X] (n : ℕ) (x : X) :
    Subsingleton (RawPositiveHomology X n) := by
  exact (Submodule.Quotient.subsingleton_iff (rawBoundaries X n)).mpr
    (rawCycles_subsingleton_mem_boundaries n x)

theorem rawHomologyMap_const (n : ℕ) (y : Y) :
    rawHomologyMap (ContinuousMap.const X y) n = 0 := by
  let p : C(X, Unit) := ContinuousMap.const X Unit.unit
  let q : C(Unit, Y) := ContinuousMap.const Unit y
  have hf : ContinuousMap.const X y = q.comp p := rfl
  haveI : Subsingleton (RawPositiveHomology Unit n) :=
    rawPositiveHomology_subsingleton n Unit.unit
  rw [hf, rawHomologyMap_comp]
  ext z
  change rawHomologyMap q n (rawHomologyMap p n z) = 0
  rw [Subsingleton.elim (rawHomologyMap p n z) 0, map_zero]

theorem rawHomologyMap_nullhomotopic (n : ℕ) (f : C(X, Y)) (y : Y)
    (H : f.Homotopy (ContinuousMap.const X y)) : rawHomologyMap f n = 0 := by
  rw [rawHomologyMap_homotopy H n, rawHomologyMap_const]

end BanachIsometric.SingularPrism
