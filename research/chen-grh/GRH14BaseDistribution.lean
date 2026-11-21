import GRHChenDistribution
import GRH14LowerTailPayment

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem base_source_distribution {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceRemainderSum N (1/500:ℝ) ≤ (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hlarge := (lower_endpoint_parameters hN).1
  have hL := target_log_lower hN
  have hLp : 0<log (N:ℝ) := by linarith only [hL]
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  let D := LiuWeight.liuSourceDEpsilon N (1/500:ℝ)
  let F := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d : ℕ => (d:ℝ)≤(N:ℝ)^(1/2-(1/500:ℝ)))
  have hD : 1≤D := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using one_le_rpow hN1
      (by norm_num : (0:ℝ)≤1/2-(1/500:ℝ))
  have hlevel : (D:ℝ)≤(N:ℝ)^(249/500:ℝ) := by
    dsimp only [D,LiuWeight.liuSourceDEpsilon]
    norm_num only [show (1/2-(1/500:ℝ))=(249/500:ℝ) by norm_num]
    exact Nat.floor_le (by positivity)
  have hsq : ∀ d ∈ F, Squarefree d := fun d hd =>
    (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd
      (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
  have hF : F ⊆ Icc 1 D := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hsq d hd).ne_zero,
      Nat.le_floor (mem_filter.mp hd).2⟩
  have hw := GRH.weighted_AP_numerical hN hD hlevel F hF hsq
  have hsum : (∑ d ∈ F, BombieriVinogradov.standardPrimeAPMaxError N d) ≤
      (1e-12:ℝ)*N/log (N:ℝ)^2 := by
    apply le_trans _ hw
    apply sum_le_sum
    intro d _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1:ℝ)≤3) : (1:ℝ)≤3^d.primeFactors.card)
      (BombieriVinogradov.standardPrimeAPMaxError_nonneg N d)
  have he := jurkatRichertSource_exceptional_endpoint_le N (1/500:ℝ)
    (by omega) (by norm_num) (by norm_num)
  have hr := jurkatRichertSourceRemainderSum_le_standardMax_add_exceptional N (1/500:ℝ) hEven hlarge
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hePow : (N:ℝ)^(1/2-(1/500:ℝ)) ≤ (N:ℝ)^(1/2:ℝ) :=
    rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have heSimple : 2*(N:ℝ)^(1/2-(1/500:ℝ))*log (N:ℝ)/log 2 ≤
      4*(N:ℝ)^(1/2:ℝ)*log (N:ℝ) := by
    apply (div_le_iff₀ hl2).mpr
    have hh := mul_le_mul_of_nonneg_right hePow hLp.le
    have hp := mul_nonneg (show 0≤(N:ℝ)^(1/2:ℝ)*log (N:ℝ) by positivity)
      (show 0≤log (2:ℝ)-1/2 by linarith only [log_two_gt_d9])
    nlinarith only [hh,hp]
  have hp := truncated_polynomial_payment hL (A:=(4000000:ℝ)) (by norm_num)
    (α:=(1/2:ℝ)) (by norm_num) (k:=3) (by norm_num)
  have hsmall : (4:ℝ)*(log (N:ℝ))^3*exp (-(1/2:ℝ)*log (N:ℝ))≤(1e-12:ℝ) := by
    nlinarith only [hp]
  have hid : 4*(N:ℝ)^(1/2:ℝ)*log (N:ℝ) =
      ((4:ℝ)*(log (N:ℝ))^3*exp (-(1/2:ℝ)*log (N:ℝ)))*((N:ℝ)/log (N:ℝ)^2) := by
    have hnp : (N:ℝ)^(1/2:ℝ)=(N:ℝ)*exp (-(1/2:ℝ)*log (N:ℝ)) := by
      calc
        _ = exp (log (N:ℝ)*(1/2:ℝ)) := rpow_def_of_pos hNp _
        _ = exp (log (N:ℝ))*exp (-(1/2:ℝ)*log (N:ℝ)) := by
          rw [← exp_add]
          congr 1
          ring
        _ = _ := by rw [exp_log hNp]
    rw [hnp]
    field_simp [hLp.ne']
  have hpaid : 4*(N:ℝ)^(1/2:ℝ)*log (N:ℝ)≤(1e-12:ℝ)*N/log (N:ℝ)^2 := by
    rw [hid]
    exact (mul_le_mul_of_nonneg_right hsmall (by positivity)).trans_eq (by ring)
  change jurkatRichertSourceRemainderSum N (1/500:ℝ)≤_ at hr
  change _ ≤ (∑ d ∈ F, BombieriVinogradov.standardPrimeAPMaxError N d)+_ at hr
  calc
    _ ≤ (∑ d ∈ F, BombieriVinogradov.standardPrimeAPMaxError N d)+
        2*(N:ℝ)^(1/2-(1/500:ℝ))*log (N:ℝ)/log 2 := hr.trans (add_le_add le_rfl he)
    _ ≤ (1e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 :=
      add_le_add hsum (heSimple.trans hpaid)
    _ = _ := by ring

theorem base_remainder_below {N L : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hlevel : (L:ℝ)≤(N:ℝ)^(249/500:ℝ)) :
    sieveRemainderBelow (jurkatRichertSourceBoundingSieve N) L ≤
      (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  apply le_trans _ (base_source_distribution hN hEven)
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    refine mem_filter.mpr ⟨(mem_filter.mp hd).1,?_⟩
    have hh : (d:ℝ)<L := by exact_mod_cast (mem_filter.mp hd).2
    norm_num only [show (1/2-(1/500:ℝ))=(249/500:ℝ) by norm_num]
    exact hh.le.trans hlevel
  · intro _ _ _
    exact abs_nonneg _

#print axioms base_source_distribution
end ChenEffective.GRH14
