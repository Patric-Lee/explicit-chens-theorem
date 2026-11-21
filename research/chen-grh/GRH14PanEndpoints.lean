import GRH14PanMoving
import BJSH30PanLedger
import BJSH30PanPrincipal

noncomputable section
namespace ChenEffective.GRH14
open Real Complex Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem pan_log_cutoff_at_target {k N : ℕ} (hk : k≤249) (hN : targetCutoff≤N) :
    logPowerCutoff k≤N := by
  apply le_trans _ hN
  rw [targetCutoff_eq]
  unfold logPowerCutoff
  apply Nat.pow_le_pow_right (by norm_num)
  have hh := Nat.pow_le_pow_left (by omega : k+1≤250) 2
  nlinarith only [hh]

theorem pan_low_at_target (U b N : ℕ) (hN : targetCutoff≤N)
    (hU : U≤32) (hb : b≤38)
    (m A₁ A₂ Q : ℕ) (g : ℕ→ℂ) (hm : 1≤m) (hmN : (m:ℝ)≤Real.sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) (hQ : (Q:ℝ)≤Real.log (N:ℝ)^b)
    (hg : ∀ a∈Ioc A₁ A₂, ‖g a‖≤1) :
    PanLow.nonprincipalLow g (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
      N A₁ A₂ Q ≤ 4*N/Real.log (N:ℝ)^U := by
  have hN9 : 9≤N := by
    have hh := pan_log_cutoff_at_target (k:=0) (by norm_num) hN
    exact (logPowerCutoff_nine_le _).trans hh
  have hAN : A₂≤N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1≤N by omega)) (by norm_num))
  have hp := PanLow.nonprincipalLow_le_prime_budget g N A₁ A₂ Q m 1
    ((U+b+2:ℕ):ℝ) (by omega) hAN (by omega) (by norm_num) hg (by
      intro a ha q hq χ
      obtain ⟨ha₁,ha₂⟩ := mem_Ioc.mp ha
      obtain ⟨hq₂,hqQ⟩ := mem_Icc.mp hq
      simpa only [Real.rpow_natCast,one_mul] using
        pan_prime_moving hN (by omega : b≤40) (by omega : U+b+2≤99)
          a (by omega) ((by exact_mod_cast ha₂ : (a:ℝ)≤A₂).trans hA)
          q hq₂ ((by exact_mod_cast hqQ : (q:ℝ)≤Q).trans hQ) χ
          (primitiveCharacter_ne_one_of_two_le hq₂ χ))
  have hpay : panBudgetThreshold U b≤N := by
    unfold panBudgetThreshold
    exact pan_log_cutoff_at_target (by omega) hN
  have hh := numerical_pan_budget U b N hpay 1 (by norm_num) m A₂ Q hm hmN hA hQ
  simp only [Real.rpow_natCast,one_mul] at hp
  norm_num only [one_mul, mul_one] at hh
  exact hp.trans hh

theorem pan_principal_at_target (s N : ℕ) (hN : targetCutoff≤N) (hs : s≤32)
    (q A₁ A₂ : ℕ) (hq : 1≤q) (hqN : (q:ℝ)≤Real.sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.principalError N A₁ A₂ q| ≤ 4*N/Real.log (N:ℝ)^s := by
  have hN9 := (logPowerCutoff_nine_le 0).trans
    (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hAN : A₂≤N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1≤N by omega)) (by norm_num))
  have hb := PanPrincipal.principalError_le_budget N A₁ A₂ q
    ((N:ℝ)/Real.log (N:ℝ)^(s+2)) (by omega) hAN (by positivity) (by
      intro a ha
      exact pan_principal_moving hN (by omega : s+2≤97) a
        (by have := (mem_Ioc.mp ha).1; omega)
        ((by exact_mod_cast (mem_Ioc.mp ha).2 : (a:ℝ)≤A₂).trans hA))
  have hpay : panBudgetThreshold s 0≤N := by
    unfold panBudgetThreshold
    exact pan_log_cutoff_at_target (by omega) hN
  have hp := numerical_pan_budget s 0 N hpay 1 (by norm_num)
    q A₂ 1 hq hqN hA (by simp)
  exact hb.trans (by simpa only [Nat.add_zero,Nat.cast_one,one_mul,show (2*1+2:ℝ)=4 by norm_num] using hp)

theorem pan_actual_paid_principal (s N : ℕ) (hN : targetCutoff≤N) (hs : s≤32)
    (B : ℝ) (q : ℕ) (hq : 1≤q) (hqN : (q:ℝ)≤Real.sqrt N) :
    liuPanActualError (2/Real.log 2) N B q ≤
      (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N B)
        (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))+
        4*N/Real.log (N:ℝ)^s)/q.totient := by
  have hp := pan_principal_at_target s N hN hs q
    (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) hq hqN
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  rw [principalError_eq_liuPanActualPrincipalRaw] at hp
  exact (liuWeight_intervalMaxL_le_nonprincipal_add_principal (2/Real.log 2)
    N (liuSourceZ10 N) (liuSourceY3 N) _ _ q hq).trans
      (div_le_div_of_nonneg_right (add_le_add le_rfl hp) (Nat.cast_nonneg _))

#print axioms pan_low_at_target
#print axioms pan_principal_at_target
end ChenEffective.GRH14


