import Mathlib.Analysis.SpecialFunctions.Exp

namespace ChenEffective

/-- A selectable ratio between the polynomial and hat error coefficients. -/
class CorrectionProfile where
  weight : ℝ
  positive : 0 < weight
  le_one : weight ≤ 1

instance defaultCorrectionProfile : CorrectionProfile where
  weight := 1
  positive := by norm_num
  le_one := le_rfl

end ChenEffective
