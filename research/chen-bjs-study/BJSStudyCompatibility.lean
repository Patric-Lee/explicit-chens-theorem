import BJSStudyChen
import Goldbach.Statement

namespace ChenEffective
theorem bjsStudy_original_chen : Goldbach.ChenTheorem :=
  ⟨bjsStudyN0,fun _ hN hEven => bjsStudy_chen hN hEven⟩
end ChenEffective
