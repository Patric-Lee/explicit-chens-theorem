import NumericalMertensGlobal
import QualitativeMertens

/-! Proof replacement: this file has no BJS imports or provisional axioms. -/
noncomputable section
namespace ChenEffective
open Real Filter AnalyticNumberTheory.Mertens
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem bjsStudy_elementary_constant : ElementaryMertens.M=mertensSecondConstant := by
  have hz : Tendsto (fun n : ℕ => 1/log (n:ℝ)) atTop (𝓝 0) := by
    have hh := tendsto_inv_atTop_zero.comp (show Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop from
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    convert hh using 1
    ext n
    simp only [Function.comp_apply,one_div]
  have hc := mertensSecond_isBigO.trans_tendsto hz
  have he : Tendsto (fun n : ℕ => primeReciprocalSum n-
      (log (log (n:ℝ))+ElementaryMertens.M)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun n : ℕ => 10/log (n:ℝ)) atTop (𝓝 0) from ?_)
    · filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
      simpa only [Real.norm_eq_abs,globalMertensBudget,Nat.cast_ofNat] using numerical_mertens_all hn
    · simpa only [div_eq_mul_inv,mul_zero,one_mul] using hz.const_mul 10
  have hd := hc.sub he
  have hh : Tendsto (fun _ : ℕ => ElementaryMertens.M-mertensSecondConstant) atTop (𝓝 0) := by
    convert hd using 1 <;> first | funext n; ring | norm_num
  exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hh)

theorem bjsStudy_reciprocal_elementary {n : ℕ} (hn : 2 ≤ n) :
    |primeReciprocalSum n-(log (log (n:ℝ))+mertensSecondConstant)| ≤ 10/log (n:ℝ) := by
  simpa only [bjsStudy_elementary_constant,globalMertensBudget,Nat.cast_ofNat] using numerical_mertens_all hn

#print axioms bjsStudy_reciprocal_elementary
end ChenEffective
