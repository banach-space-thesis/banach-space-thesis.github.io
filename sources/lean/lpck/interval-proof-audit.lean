import LPCK.IntervalAssembly
#check LPCK.theorem_1_2_proof
#print axioms LPCK.theorem_1_2_proof
#print axioms ThesisCommon.interval_hasCPFP_four
example (p : ThesisCommon.BanachExponent) : LPCK.Theorem_1_2 ℝ p :=
  LPCK.theorem_1_2_proof p
example (p : ThesisCommon.BanachExponent) : LPCK.Theorem_1_2 ℂ p :=
  LPCK.theorem_1_2_proof p
