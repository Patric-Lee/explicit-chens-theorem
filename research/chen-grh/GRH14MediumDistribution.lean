import GRH14MediumTailPayment
import GRH14BaseDistribution
import NumericalPreSieveDistribution

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem varying_correction_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    jurkatRichertSourceVaryingQUnconditionalCorrection N (1/500:ℝ) ≤
      (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hlarge := (lower_endpoint_parameters hN).1
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN9 : 9≤N := by
    have hh := log_le_sub_one_of_pos hn
    exact_mod_cast (by linarith only [hh,hL] : (9:ℝ)≤N)
  have hb := numerical_varying_correction hN9 (by norm_num : (0:ℝ)≤1/500)
  have hp := truncated_polynomial_payment hL (A:=(3000000000:ℝ)) (by norm_num)
    (α:=(1/10:ℝ)) (by norm_num) (k:=9) (by norm_num)
  have hs : (3000:ℝ)*(log (N:ℝ))^9*exp (-(1/10:ℝ)*log (N:ℝ))≤(1e-12:ℝ) := by
    nlinarith only [hp]
  have hid : (N:ℝ)^(9/10:ℝ)=(N:ℝ)*exp (-(1/10:ℝ)*log (N:ℝ)) := by
    calc
      _ = exp (log (N:ℝ)*(9/10:ℝ)) := rpow_def_of_pos hn _
      _ = exp (log (N:ℝ))*exp (-(1/10:ℝ)*log (N:ℝ)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = _ := by rw [exp_log hn]
  apply hb.trans
  calc
    _ = ((3000:ℝ)*(log (N:ℝ))^9*exp (-(1/10:ℝ)*log (N:ℝ)))*
        ((N:ℝ)/log (N:ℝ)^2) := by rw [hid]; field_simp [hl.ne']
    _ ≤ (1e-12:ℝ)*((N:ℝ)/log (N:ℝ)^2) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

theorem medium_source_distribution {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    preSieveVaryingRemainder N (1/500:ℝ) ≤ (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hh := preSieve_unweighted_varying_remainder_le_BV N (1/500:ℝ) hEven
    (lower_endpoint_parameters hN).1
  have hw := GRH.chen_weighted_distribution hN
  have hc := varying_correction_at_target hN
  calc
    _ ≤ _ := hh
    _ ≤ (1e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 := add_le_add hw hc
    _ = _ := by ring

theorem medium_truncated_remainders {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (D : ℕ → ℕ) (hD : ∀ q ∈ jurkatRichertSourceMediumPrimes N, 1≤D q)
    (hDN : ∀ q ∈ jurkatRichertSourceMediumPrimes N, D q≤N)
    (hlevel : ∀ q ∈ jurkatRichertSourceMediumPrimes N,
      preSieveTruncation N*D q≤jurkatRichertSourceUpperLevel N q (1/500:ℝ)) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      GRH.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q) 4000000
        (D q) (preSieveTruncation N)) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hl : (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      sieveRemainderBelow (jurkatRichertSourceConditionedBoundingSieve N q)
        (preSieveTruncation N*D q)) ≤ preSieveVaryingRemainder N (1/500:ℝ) := by
    apply sum_le_sum
    intro q hq
    exact sieveRemainderBelow_mono _ (hlevel q hq)
  have ht := medium_tail_paid_at_target hN hEven D hD hDN
  unfold GRH.truncatedRemainderBound
  rw [sum_add_distrib]
  calc
    _ ≤ preSieveVaryingRemainder N (1/500:ℝ)+(1e-12:ℝ)*N/log (N:ℝ)^2 := add_le_add hl ht
    _ ≤ (2e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 :=
      add_le_add (medium_source_distribution hN hEven) le_rfl
    _ = _ := by ring

theorem base_truncated_remainder {N D : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hD : 1≤D) (hDN : D≤N)
    (hlevel : ((preSieveTruncation N*D:ℕ):ℝ)≤(N:ℝ)^(249/500:ℝ)) :
    GRH.truncatedRemainderBound (jurkatRichertSourceBoundingSieve N) 4000000 D
      (preSieveTruncation N) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hl := base_remainder_below hN hEven hlevel
  have ht := source_tail_paid_at_target hN hEven hD hDN
  unfold GRH.truncatedRemainderBound
  calc
    _ ≤ (2e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 := add_le_add hl ht
    _ = _ := by ring

#print axioms medium_truncated_remainders
#print axioms base_truncated_remainder
end ChenEffective.GRH14
