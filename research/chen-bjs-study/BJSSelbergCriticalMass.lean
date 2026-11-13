import BJSSelbergCriticalKernel
import NumericalSelbergDivisorGeometry

noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def selbergCriticalHalfWeight (N n : ℕ) : ℝ :=
  |selbergCriticalCorrection N n| * sqrt n

def selbergCriticalHalfMajorant (N n : ℕ) : ℝ :=
  (if n∈N.primeFactors then 4/sqrt n else 0)+24*(n:ℝ)^(-(3/2:ℝ))

theorem critical_half_majorant_summable (N : ℕ) : Summable (selbergCriticalHalfMajorant N) := by
  apply Summable.add
  · exact summable_of_ne_finset_zero (s:=N.primeFactors) (by intro n hn; simp [hn])
  · exact (Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).mul_left 24

theorem critical_half_majorant_mass {N : ℕ} (hN : 0<N) :
    (∑' n,selbergCriticalHalfMajorant N n) ≤ 1096+log (N:ℝ)/16 := by
  have hs : Summable (fun n : ℕ => if n∈N.primeFactors then (4:ℝ)/sqrt n else 0) :=
    summable_of_ne_finset_zero (s:=N.primeFactors) (by intro n hn; simp [hn])
  have hr := Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)
  have hfinite : (∑' n : ℕ,if n∈N.primeFactors then (4:ℝ)/sqrt n else 0)=
      ∑ n∈N.primeFactors,4/sqrt n := by
    rw [tsum_eq_sum (s:=N.primeFactors) (by intro n hn; simp [hn])]
    exact sum_congr rfl (by intro n hn; simp [hn])
  have hsmall : (∑ p∈N.primeFactors.filter (fun p => p<256), (4:ℝ)/sqrt p) ≤ 1024 := by
    have hcard : (N.primeFactors.filter (fun p => p<256)).card≤256 := by
      apply (card_le_card (show N.primeFactors.filter (fun p => p<256) ⊆ range 256 by
        intro p hp; exact mem_range.mpr (mem_filter.mp hp).2)).trans
      simp
    calc
      _ ≤ ∑ p∈N.primeFactors.filter (fun p => p<256),(4:ℝ) := by
        apply sum_le_sum
        intro p hp
        have hp2 := (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
        have hh : (1:ℝ)≤sqrt p := one_le_sqrt.mpr (by exact_mod_cast (show 1≤p by omega))
        exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hh)).mpr (by linarith)
      _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; exact_mod_cast (by omega :
        (N.primeFactors.filter (fun p => p<256)).card*4≤1024)
  have hlarge : (∑ p∈N.primeFactors.filter (fun p => ¬p<256),(4:ℝ)/sqrt p) ≤ log (N:ℝ)/16 := by
    calc
      _ ≤ ∑ p∈N.primeFactors.filter (fun p => ¬p<256),log (p:ℝ)/16 := by
        apply sum_le_sum
        intro p hp
        have hp256 : 256≤p := by have := (mem_filter.mp hp).2; omega
        have hs16 : (16:ℝ)≤sqrt p := (le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast hp256)
        have hl256 : (4:ℝ)≤log (256:ℝ) := by
          rw [show (256:ℝ)=2^8 by norm_num,log_pow]
          norm_num only [Nat.cast_ofNat]
          linarith only [log_two_gt_d9]
        have hlp := hl256.trans (log_le_log (by norm_num : (0:ℝ)<256) (by exact_mod_cast hp256 : (256:ℝ)≤p))
        have hdiv : (4:ℝ)/sqrt p≤1/4 := (div_le_iff₀ (by linarith only [hs16])).mpr (by linarith only [hs16])
        linarith only [hdiv,hlp]
      _ ≤ _ := by
        rw [← sum_div]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => log_natCast_nonneg p)).trans
          (sum_log_primeFactors_le_log hN)
  have hsplit := sum_filter_add_sum_filter_not (s:=N.primeFactors)
    (p:=fun p => p<256) (f:=fun p => (4:ℝ)/sqrt p)
  have htail := tsum_nat_rpow_neg_le (3/2) (by norm_num)
  norm_num only [show (3/2:ℝ)-1=1/2 by norm_num,one_div_div,div_one] at htail
  unfold selbergCriticalHalfMajorant
  rw [hs.tsum_add (hr.mul_left 24),hfinite,tsum_mul_left]
  linarith only [hsmall,hlarge,hsplit,htail]

theorem sqrt_nat_pow (p k : ℕ) : sqrt ((p^k:ℕ):ℝ)=(sqrt (p:ℝ))^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,Nat.cast_mul,sqrt_mul (Nat.cast_nonneg _),ih,pow_succ]

theorem critical_half_local {N p : ℕ} (hEven : Even N) (hp : p.Prime) :
    let r : ℝ := 1/sqrt p
    let B : ℝ := if p∣N then 1 else 2/((p:ℝ)-2)
    ∀ k : ℕ,selbergCriticalHalfWeight N (p^k)=
      if k=0 then 1 else B*r^k := by
  intro r B k
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hs0 : 0<sqrt (p:ℝ) := sqrt_pos.mpr hp0
  have hs : sqrt (p:ℝ)/(p:ℝ)=1/sqrt p := sqrt_div_self'
  by_cases hk : k=0
  · subst k
    simp [selbergCriticalHalfWeight,show selbergCriticalCorrection N 1=1 from
      (selberg_critical_multiplicative N).1]
  rw [if_neg hk]
  unfold selbergCriticalHalfWeight
  rw [selberg_critical_prime_pow hp,sqrt_nat_pow]
  unfold selbergCriticalLocal
  rw [if_neg hk]
  by_cases hpd : p∣N
  · rw [if_pos hpd]
    dsimp only [B]
    rw [if_pos hpd]
    simp only [abs_pow,abs_div,abs_neg,abs_one,abs_of_pos hp0,one_div]
    rw [← mul_pow,show (p:ℝ)⁻¹*sqrt p=1/sqrt p by rw [mul_comm,← div_eq_mul_inv,hs]]
    simp only [r,one_mul]
  · have hp2 : 2<p := by
      have hpne : p≠2 := by intro he; subst p; exact hpd hEven.two_dvd
      have := hp.two_le
      omega
    have hp2R : 0<(p:ℝ)-2 := by
      have hpR : (2:ℝ)<p := by exact_mod_cast hp2
      linarith
    rw [if_neg hpd]
    dsimp only [B]
    rw [if_neg hpd]
    simp only [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,abs_of_pos hp0,
      abs_of_pos hp2R,abs_of_pos (by norm_num : (0:ℝ)<2)]
    rw [mul_one,div_eq_mul_inv,mul_assoc,← inv_pow,← mul_pow,
      show (p:ℝ)⁻¹*sqrt p=1/sqrt p by rw [mul_comm,← div_eq_mul_inv,hs]]

theorem critical_half_local_mass {N p : ℕ} (hEven : Even N) (hN : 0<N) (hp : p.Prime) :
    Summable (fun k => selbergCriticalHalfWeight N (p^k)) ∧
    (∑' k,selbergCriticalHalfWeight N (p^k)) ≤ exp (selbergCriticalHalfMajorant N p) := by
  let r : ℝ := 1/sqrt p
  let B : ℝ := if p∣N then 1 else 2/((p:ℝ)-2)
  have hp2 := hp.two_le
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hs : 0<sqrt (p:ℝ) := sqrt_pos.mpr hp0
  have hsq := sq_sqrt hp0.le
  have hslo : (4/3:ℝ)≤sqrt p := (le_sqrt (by norm_num) hp0.le).mpr (by
    have h2 : (2:ℝ)≤p := by exact_mod_cast hp2
    linarith only [h2])
  have hr0 : 0≤r := by positivity
  have hr : r≤3/4 := (div_le_iff₀ hs).mpr (by linarith only [hslo])
  have hr1 : r<1 := by linarith only [hr]
  have hgeo := hasSum_geometric_of_lt_one hr0 hr1
  have heq : (fun k => selbergCriticalHalfWeight N (p^k)) =
      fun k => (if k=0 then (1:ℝ)-B else 0)+B*r^k := by
    funext k
    rw [critical_half_local hEven hp k]
    by_cases hk : k=0 <;> simp [hk,r,B]
  have hsingle : Summable (fun k : ℕ => if k=0 then (1:ℝ)-B else 0) :=
    summable_of_ne_finset_zero (s:={0}) (by intro k hk; simp only [mem_singleton] at hk; simp [hk])
  have hsum : Summable (fun k => selbergCriticalHalfWeight N (p^k)) := by
    rw [heq]; exact hsingle.add (hgeo.summable.mul_left B)
  have htotal : (∑' k,selbergCriticalHalfWeight N (p^k))=1+B*r/(1-r) := by
    rw [heq,hsingle.tsum_add (hgeo.summable.mul_left B),tsum_mul_left,hgeo.tsum_eq]
    simp only [tsum_ite_eq]
    field_simp [ne_of_gt (sub_pos.mpr hr1)]
    ring
  have hbudget : B*r/(1-r)≤selbergCriticalHalfMajorant N p := by
    have hp_mem : p∈N.primeFactors ↔ p∣N := by
      rw [Nat.mem_primeFactors]; exact ⟨fun h => h.2.1,fun h => ⟨hp,h,by omega⟩⟩
    by_cases hpd : p∣N
    · have hb : B=1 := by simp [B,hpd]
      have hh : r/(1-r)≤4/sqrt p := by
        apply (div_le_iff₀ (by linarith only [hr] : 0<1-r)).mpr
        dsimp only [r] at *
        field_simp
        nlinarith only [hslo]
      rw [hb,one_mul]
      exact hh.trans (by
        simp only [selbergCriticalHalfMajorant,if_pos (hp_mem.mpr hpd)]
        exact le_add_of_nonneg_right (by positivity))
    · have hp3 : 3≤p := by
        have hn : p≠2 := by intro he; subst p; exact hpd hEven.two_dvd
        omega
      have hpR : (3:ℝ)≤p := by exact_mod_cast hp3
      have hden : 0<(p:ℝ)-2 := by linarith only [hpR]
      have hh : B*r/(1-r)≤24/((p:ℝ)*sqrt p) := by
        dsimp only [B,r]
        rw [if_neg hpd]
        apply (div_le_iff₀ (by linarith only [hr] : 0<1-r)).mpr
        field_simp
        nlinarith [sq_nonneg (sqrt (p:ℝ)-2),mul_nonneg (by linarith only [hpR] : 0≤(p:ℝ)-3) (by linarith only [hslo] : 0≤sqrt (p:ℝ)-1)]
      have hid : (p:ℝ)^(-(3/2:ℝ))=1/((p:ℝ)*sqrt p) := by
        rw [rpow_neg hp0.le,show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hp0,
          rpow_one,← sqrt_eq_rpow,one_div]
      simpa only [selbergCriticalHalfMajorant,if_neg (mt hp_mem.mp hpd),zero_add,hid,mul_one_div] using hh
  refine ⟨hsum,?_⟩
  rw [htotal]
  have hexp : 1+selbergCriticalHalfMajorant N p≤exp (selbergCriticalHalfMajorant N p) := by
    simpa only [add_comm] using add_one_le_exp (selbergCriticalHalfMajorant N p)
  exact (add_le_add_right hbudget 1).trans (by simpa only [add_comm] using hexp)

theorem selberg_critical_half_mass {N : ℕ} (hEven : Even N) (hN : 0<N) :
    Summable (selbergCriticalHalfWeight N) ∧
    (∑' n,selbergCriticalHalfWeight N n) ≤ exp (1096+log (N:ℝ)/16) := by
  apply numerical_multiplicative_mass (selbergCriticalHalfWeight N)
    (selbergCriticalHalfMajorant N) (1096+log (N:ℝ)/16)
  · simp [selbergCriticalHalfWeight]
  · simp [selbergCriticalHalfWeight,(selberg_critical_multiplicative N).1]
  · intro n; exact mul_nonneg (abs_nonneg _) (sqrt_nonneg _)
  · intro m n hmn
    dsimp only [selbergCriticalHalfWeight]
    rw [(selberg_critical_multiplicative N).map_mul_of_coprime hmn,abs_mul,
      Nat.cast_mul,sqrt_mul (Nat.cast_nonneg _)]
    ring
  · intro p hp; exact (critical_half_local_mass hEven hN hp).1
  · exact critical_half_majorant_summable N
  · intro n
    unfold selbergCriticalHalfMajorant
    apply add_nonneg
    · split_ifs <;> positivity
    · positivity
  · exact critical_half_majorant_mass hN
  · intro p hp; exact (critical_half_local_mass hEven hN hp).2

#print axioms selberg_critical_half_mass
end ChenEffective
