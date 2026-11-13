import BJSH30MassCap
import BJSH30BaseDistribution
import BJSH30Geometry
import BJSJointBudget

noncomputable section
namespace ChenEffective.H30
open Real
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 3000000

theorem medium_mass_allocation {B J : ℝ} (hB : B≤25/2) (hJ : J≤120) :
    (B+300/5000000)*(J+1/10000+(7/125)*(8/5))+1/5000000≤B*J+113/100 := by
  nlinarith only [hB,hJ]

theorem target_margin : (jointSelbergBudget (8.2:ℝ) (1/10000) 0 (1/100)).margin=0.000926 := by
  rw [joint_selberg_margin]
  norm_num

theorem fixed_base_distribution {N : ℕ} (hN : distributionThreshold≤N) (hEven : Even N) :
    jurkatRichertSourceRemainderSum N (1/(1200000000:ℝ))≤
      (1/20000000:ℝ)*SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by
  exact base_distribution_paid 1200000000 20000000 N (by norm_num) (by norm_num) (by norm_num)
    hN (by norm_num [highBVExponent]) hEven

theorem fixed_varying_distribution {N : ℕ} (hN : distributionThreshold≤N) (hEven : Even N) :
    jurkatRichertSourceVaryingQRemainderSum N (1/(600000000:ℝ))≤
      (1/5000000:ℝ)*SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by
  exact varying_distribution_paid 600000000 5000000 N (by norm_num) (by norm_num) (by norm_num)
    hN (by norm_num [highBVExponent,weightedSaving]) hEven

#print axioms fixed_base_distribution
#print axioms fixed_varying_distribution
end ChenEffective.H30
