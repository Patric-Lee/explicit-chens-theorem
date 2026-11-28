import GRHQuarterChenCore

/- Component: GRHQuarterChenLowerFactor -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem inner_integral_quarter {u : ℝ} (hu3 : 3≤ u) (hu4 : u≤4) :
    0≤ jurkatRichertInnerIntegral u ∧ jurkatRichertInnerIntegral u≤1/4 := by
  have hcont : ContinuousOn (fun t : ℝ => log (t-1)/t) (Icc 2 (u-1)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t-1≠0
      linarith only [ht.1]
    · exact continuousOn_id
    · intro t ht
      linarith only [ht.1]
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (show (2:ℝ)≤ u-1 by linarith) hcont
  have hpoint (t : ℝ) (ht : t∈Icc 2 (u-1)) : log (t-1)/t≤(t-2)/2 := by
    have ht0 : 0<t := by linarith only [ht.1]
    have hl := log_le_sub_one_of_pos (show 0<t-1 by linarith only [ht.1])
    apply (div_le_iff₀ ht0).mpr
    nlinarith only [hl,sq_nonneg (t-2)]
  have hbound : jurkatRichertInnerIntegral u ≤ (u-3)^2/4 := by
    unfold jurkatRichertInnerIntegral
    calc
      _ ≤ ∫ t in (2:ℝ)..u-1, (t-2)/2 :=
        intervalIntegral.integral_mono_on (by linarith) hi
          (((continuous_id.sub continuous_const).div_const 2).intervalIntegrable _ _) hpoint
      _ = _ := by
        have heq : (∫ t in (2:ℝ)..u-1, t-2) =
            (∫ t in (2:ℝ)..u-1, t) - ∫ _t in (2:ℝ)..u-1, (2:ℝ) :=
          intervalIntegral.integral_sub (continuous_id.intervalIntegrable _ _) intervalIntegrable_const
        rw [intervalIntegral.integral_div,heq,integral_id,intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  refine ⟨(numerical_inner_integral hu3 hu4).1,?_⟩
  nlinarith only [hbound,hu3,hu4,mul_nonneg (show 0≤ u-3 by linarith) (show 0≤4-u by linarith)]

theorem lower_factor_scaled_loss {s : ℝ} (hs : (49/10:ℝ)≤ s) (hs5 : s≤5) :
    jurkatRichertMertensFactor*
      (dimensionOneLowerLinearSieveFactor 5-dimensionOneLowerLinearSieveFactor s) ≤
        (41/100:ℝ)*(5-s) := by
  let B := fun t : ℝ => log (t-1)+∫ u in (3:ℝ)..t-1, jurkatRichertInnerIntegral u/u
  have hs0 : 0<s := by linarith only [hs]
  have hsp : 0<s-1 := by linarith only [hs]
  have h3s : (3:ℝ)≤ s-1 := by linarith only [hs]
  have hs4 : s-1≤(4:ℝ) := by linarith only [hs5]
  have hδ : 0≤5-s := by linarith only [hs5]
  have hi1 := numerical_outer_interval (le_refl (3:ℝ)) h3s hs4
  have hi2 := numerical_outer_interval h3s hs4 (le_refl (4:ℝ))
  have hl : log 4-log (s-1) ≤ (5-s)/(s-1) := by
    have hh := log_le_sub_one_of_pos (show 0<(4:ℝ)/(s-1) by positivity)
    rw [log_div (by norm_num) hsp.ne'] at hh
    convert hh using 1 <;> field_simp <;> ring
  have hint : (∫ u in s-1..(4:ℝ), jurkatRichertInnerIntegral u/u) ≤
      (5-s)/(4*(s-1)) := by
    calc
      _ ≤ ∫ _u in s-1..(4:ℝ), (1/4:ℝ)/(s-1) := by
        apply intervalIntegral.integral_mono_on hs4 hi2 intervalIntegrable_const
        intro u hu
        have hu0 : 0<u := by linarith only [h3s,hu.1]
        apply (div_le_div_of_nonneg_right (inner_integral_quarter (h3s.trans hu.1) hu.2).2 hu0.le).trans
        exact div_le_div_of_nonneg_left (by norm_num) hsp hu.1
      _ = _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]; field_simp [hsp.ne'] <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hsum : B 5-B s ≤ (5/4:ℝ)*(5-s)/(s-1) := by
    dsimp only [B]
    norm_num only [show (5:ℝ)-1=4 by norm_num]
    have heq : (5-s)/(s-1)+(5-s)/(4*(s-1))=(5/4:ℝ)*(5-s)/(s-1) := by field_simp [hsp.ne'] <;> ring
    linarith only [hl,hint,hadd,heq]
  have hdiff : B 5-B s ≤ (25/78:ℝ)*(5-s) := by
    apply hsum.trans
    apply (div_le_iff₀ hsp).mpr
    nlinarith only [mul_nonneg hδ (show 0≤ s-49/10 by linarith only [hs])]
  have hlog39 : (27/20:ℝ)≤ log (39/10:ℝ) := by
    have hh := sum_range_le_log_div (by norm_num : (0:ℝ)≤29/49)
      (by norm_num : (29/49:ℝ)<1) 3
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hBs : (27/20:ℝ)≤ B s := by
    have hlog := log_le_log (by norm_num : (0:ℝ)<39/10) (show (39/10:ℝ)≤ s-1 by linarith only [hs])
    have hI : 0≤∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u := by
      apply intervalIntegral.integral_nonneg h3s
      intro u hu
      exact (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).1
    dsimp only [B]
    linarith only [hlog,hlog39,hI]
  have hquot : (27/100:ℝ)≤ B s/s := (le_div_iff₀ hs0).mpr (by linarith only [hBs,hs5])
  have hcompare : (27/500:ℝ)*(5-s)≤ B s/s-B s/5 := by
    have hh := mul_le_mul_of_nonneg_right hquot hδ
    have heq : (B s/s)*(5-s)=5*(B s/s-B s/5) := by field_simp <;> ring
    linarith only [hh,heq]
  have hscaled : B 5/5-B s/s ≤ (41/4000:ℝ)*(5-s) := by
    nlinarith only [hdiff,hcompare,hδ]
  have hcancel : jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant)=40 := by
    unfold jurkatRichertMertensFactor
    have hh : exp (-eulerMascheroniConstant)*exp eulerMascheroniConstant=1 := by
      rw [← exp_add,neg_add_cancel,exp_zero]
    nlinarith only [hh]
  calc
    _ = (jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant))*(B 5/5-B s/s) := by
      unfold dimensionOneLowerLinearSieveFactor
      dsimp only [B]
      ring
    _ = 40*(B 5/5-B s/s) := by rw [hcancel]
    _ ≤ _ := by linarith only [hscaled]

theorem lower_hat_window {s : ℝ} (hs : (49/10:ℝ)≤ s) :
    exp 2*sieveHat s ≤ (1/28:ℝ) := by
  have he := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤29/10) 7
  norm_num [Finset.sum_range_succ] at he
  have he' : (120/7:ℝ)≤ exp (29/10) := by linarith only [he]
  have hid : exp 2*exp (-(49/10:ℝ))*exp (29/10)=1 := by
    rw [← exp_add,← exp_add]
    norm_num
  calc
    _ ≤ exp 2*sieveHat (49/10) := mul_le_mul_of_nonneg_left (sieveHat_antitone hs) (exp_pos 2).le
    _ = (30/49)/exp (29/10) := by
      norm_num [sieveHat]
      field_simp
      nlinarith only [hid]
    _ ≤ _ := (div_le_iff₀ (exp_pos _)).mpr (by linarith only [he'])

theorem lower_factor_upper {s : ℝ} (hs : (4:ℝ)≤ s) (hs5 : s≤5) :
    dimensionOneLowerLinearSieveFactor s ≤ 6 := by
  have hs0 : 0<s := by linarith only [hs]
  have h3s : (3:ℝ)≤ s-1 := by linarith only [hs]
  have hs4 : s-1≤(4:ℝ) := by linarith only [hs5]
  have hI0 : 0≤∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u := by
    apply intervalIntegral.integral_nonneg h3s
    intro u hu
    exact (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).1
  have hI : (∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u)≤1 := by
    calc
      _ ≤ ∫ _u in (3:ℝ)..s-1, (1:ℝ) := intervalIntegral.integral_mono_on h3s
        (numerical_outer_interval (le_refl (3:ℝ)) h3s hs4) intervalIntegrable_const
        (fun u hu => (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).2)
      _ = s-4 := by simp; ring
      _ ≤ 1 := by linarith only [hs5]
  have hlog0 : 0≤ log (s-1) := log_nonneg (by linarith only [hs])
  have hlog : log (s-1)≤3 := (log_le_sub_one_of_pos (by linarith only [hs])).trans (by linarith only [hs5])
  have he : exp eulerMascheroniConstant≤3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have hquot : 2*exp eulerMascheroniConstant/s≤3/2 :=
    (div_le_iff₀ hs0).mpr (by linarith only [he,hs])
  unfold dimensionOneLowerLinearSieveFactor
  apply (mul_le_mul hquot (show log (s-1)+(∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u)≤4 by linarith only [hlog,hI])
    (by linarith only [hlog0,hI0]) (by norm_num)).trans
  norm_num

theorem mertens_factor_lower_one : (1:ℝ)≤ jurkatRichertMertensFactor := by
  have he : exp eulerMascheroniConstant≤3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have hb : 0≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hc : jurkatRichertMertensFactor*exp eulerMascheroniConstant=20 := by
    unfold jurkatRichertMertensFactor
    rw [mul_assoc,← exp_add,neg_add_cancel,exp_zero,mul_one]
  have hh := mul_le_mul_of_nonneg_left he hb
  linarith only [hh,hc]

theorem lower_density_budget {s : ℝ} (hs : (4911/1000:ℝ)≤ s) (hs5 : s≤5) :
    jurkatRichertBaseMainCoefficient jurkatRichertJ-(62/1000:ℝ) ≤
      jurkatRichertMertensFactor*(dimensionOneLowerLinearSieveFactor s-
        110*(1/2000:ℝ)*exp 2*sieveHat s) := by
  have hscaled := lower_factor_scaled_loss (show (49/10:ℝ)≤ s by linarith only [hs]) hs5
  have hhat := lower_hat_window (show (49/10:ℝ)≤ s by linarith only [hs])
  have hBpos : 0≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hh := mul_le_mul budget_mertens_factor_cap hhat
    (mul_nonneg (exp_pos 2).le (sieveHat_pos s).le) (by norm_num : (0:ℝ)≤25/2)
  rw [dimensionOneLowerLinearSieveFactor_five] at hscaled
  have hab := jurkatRichert_sieveFactor_mul_mertensFactor
  nlinarith only [hscaled,hh,hs,hs5,hab]

#print axioms lower_density_budget
#print axioms lower_factor_scaled_loss
#print axioms lower_hat_window
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenRelativeProduct -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
variable [Fact HybridProduct.HybridPrefixWindow]
open Real Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- This generic counting proof takes a proved window as an explicit instance.
The concrete Platt-backed witness is supplied in BJSH29ConditionalChen. -/
theorem reciprocal_prefix_window : HybridProduct.HybridPrefixWindow :=
  Fact.out

noncomputable def lowerPresieveStart : ℝ := 4000000

theorem lower_interval_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : lowerPresieveStart ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) :=
  HybridProduct.hybrid_interval_product reciprocal_prefix_window s hs u z hu huz hinterval

theorem lower_presieved_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hpresieve : ∀ p ∈ s, lowerPresieveStart ≤ (p : ℝ))
    (u z : ℝ) (hu : 1 < u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) := by
  by_cases hUu : lowerPresieveStart ≤ u
  · exact lower_interval_product s hs u z hUu huz hinterval
  have huU : u ≤ lowerPresieveStart := le_of_not_ge hUu
  have hlu : 0 < log u := log_pos hu
  have hlz : 0 < log z := log_pos (hu.trans_le huz)
  by_cases hzU : z ≤ lowerPresieveStart
  · have hempty : s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      linarith only [hpresieve p hp,(hinterval p hp).2,hzU]
    rw [hempty,Finset.prod_empty]
    have hr : 1 ≤ log z/log u := (le_div_iff₀ hlu).mpr
      (by simpa using log_le_log (by linarith only [hu] : 0 < u) huz)
    nlinarith only [hr,(by norm_num : (0:ℝ) ≤ 1/4000)]
  have hUz : lowerPresieveStart ≤ z := le_of_not_ge hzU
  apply (lower_interval_product s hs lowerPresieveStart z le_rfl hUz
    (fun p hp => ⟨hpresieve p hp,(hinterval p hp).2⟩)).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [(by norm_num : (0:ℝ) ≤ 1/4000)])
  exact div_le_div_of_nonneg_left hlz.le hlu (log_le_log (by linarith only [hu] : 0 < u) huU)


theorem lower_product_relative (S : BoundingSieve)
    (hodd : ∀ p ∈ S.prodPrimes.primeFactors, 2 < p)
    (hnu : ∀ p ∈ S.prodPrimes.primeFactors, S.nu p=1/((p : ℝ)-1)) :
    HasRelativeSieveProduct (preSieveCounting S lowerPresieveStart) (1/4000:ℝ) := by
  intro u z hu huz
  unfold suzukiLocalRatio
  change (∏ p ∈ (restrictSievePrimes S lowerPresieveStart).prodPrimes.primeFactors.filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z), (1-S.nu p)⁻¹) ≤ _
  rw [restrictSievePrimes_primeFactors]
  let s := (S.prodPrimes.primeFactors.filter (fun p : ℕ => lowerPresieveStart ≤ (p : ℝ))).filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hP := (mem_filter.mp (mem_filter.mp hp).1).1
    exact ⟨Nat.prime_of_mem_primeFactors hP,hodd p hP⟩
  have hid : (∏ p ∈ s, (1-S.nu p)⁻¹) = ∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹ := by
    apply prod_congr rfl
    intro p hp
    rw [hnu p (mem_filter.mp (mem_filter.mp hp).1).1]
  change (∏ p ∈ s, (1-S.nu p)⁻¹) ≤ _
  rw [hid]
  exact lower_presieved_product s hs (fun _ hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    u z hu huz (fun _ hp => (mem_filter.mp hp).2)


#print axioms lower_product_relative
theorem lower_source_relative (N : ℕ) :
    HasRelativeSieveProduct (preSieveCounting (jurkatRichertSourceBoundingSieve N) 4000000)
      (1/4000:ℝ) := by
  apply lower_product_relative
  · intro p hp
    exact (prime_dvd_jurkatRichertSourceSiftingProduct (Nat.prime_of_mem_primeFactors hp)).mp
      (Nat.dvd_of_mem_primeFactors hp) |>.1
  · intro p hp
    exact AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (Nat.prime_of_mem_primeFactors hp)

theorem lower_conditioned_relative (N q : ℕ) :
    HasRelativeSieveProduct (preSieveCounting (jurkatRichertSourceConditionedBoundingSieve N q) 4000000)
      (1/4000:ℝ) := lower_source_relative N

end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenBaseCandidates -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem base_candidates_at_target {N : ℕ} (hN : targetCutoff   ≤   N) (hEven : Even N) :
    (jurkatRichertBaseMainCoefficient jurkatRichertJ-(63/1000:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2)   ≤
      ((jurkatRichertSourceCandidates N).card:ℝ) := by
  let S := jurkatRichertSourceBoundingSieve N
  let s := lowerRatio N 1
  let D := lowerLevel N 1
  let Z := Nat.ceil ((D:ℝ)^(1/s))
  let c := dimensionOneLowerLinearSieveFactor s-110*(1/2000:ℝ)*exp 2*sieveHat s
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let B := jurkatRichertMertensFactor
  let A := jurkatRichertBaseMainCoefficient jurkatRichertJ
  have hNbig := (lower_endpoint_parameters hN).1
  have hbase := lower_base_ratio hN
  have hslo : 4  ≤  s := by dsimp only [s]; linarith only [hbase.1]
  have hshi : s  ≤  5 := hbase.2
  obtain ⟨hD,hZD,hroot,hlevel⟩ := lower_level_geometry hN (q:=1) (by norm_num)
    (show 3/2  ≤  s by linarith only [hslo])
  have hDN : D  ≤  N := lower_level_le_endpoint hN (q:=1) (by norm_num) (by linarith only [hslo])
  have hcut : ∀ p ∈ (preSieveCounting S 4000000).prodPrimes.primeFactors, p<Z := by
    intro p hp
    change p∈(restrictSievePrimes S 4000000).prodPrimes.primeFactors at hp
    rw [restrictSievePrimes_primeFactors] at hp
    have hpf := (mem_filter.mp hp).1
    have hh := (prime_dvd_jurkatRichertSourceSiftingProduct (Nat.prime_of_mem_primeFactors hpf)).mp
      (Nat.dvd_of_mem_primeFactors hpf) |>.2.1
    exact Nat.lt_ceil.mpr (hh.trans_lt hroot)
  have hmass0 : 0  ≤  S.totalMass := LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2)
    (by positivity) (by exact_mod_cast (show 2  ≤  N by omega))
  have hfinite := QuarterTruncation.truncated_preSieveCounting_lower_bound S 4000000 hmass0
    (by norm_num : (0:ℝ)  ≤  1/4000) le_rfl (lower_source_relative N)
    D Z (preSieveTruncation N) (truncation_log_lower hN).1 hD hslo hshi rfl hZD hcut
  have hrem := base_truncated_remainder hN hEven (show 1  ≤  D by omega) hDN
    (by simpa only [Nat.one_mul] using hlevel)
  change QuarterTruncation.truncatedRemainderBound S 4000000 D (preSieveTruncation N) ≤
    (3e-12:ℝ)*N/log (N:ℝ)^2 at hrem
  have hM0 : 0  ≤  M := by dsimp [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hBpos : 0<B := by dsimp [B]; unfold jurkatRichertMertensFactor; positivity
  have hBmin : (1:ℝ)  ≤  B := mertens_factor_lower_one
  have hcoef : A-62/1000  ≤  B*c := lower_density_budget hbase.1 hbase.2
  have hAmin : (2/5:ℝ)  ≤  A := by
    have hh := mul_le_mul_of_nonneg_right numerical_base_factor_caps.1 hBpos.le
    have hab := jurkatRichert_sieveFactor_mul_mertensFactor
    have hb := mul_le_mul_of_nonneg_left hBmin (by norm_num : (0:ℝ)  ≤  2/5)
    dsimp only [A,B] at *
    nlinarith only [hh,hab,hb]
  have hc0 : 0  ≤  c := by
    by_contra hh
    have hm := mul_neg_of_pos_of_neg hBpos (lt_of_not_ge hh)
    linarith only [hm,hcoef,hAmin]
  have hc6 : c  ≤  6 := by
    have hh := lower_factor_upper hslo hshi
    have hp : 0  ≤  110*(1/2000:ℝ)*exp 2*sieveHat s := by
      exact mul_nonneg (by positivity) (sieveHat_pos s).le
    dsimp only [c]
    linarith only [hh,hp]
  have hmass := (source_mass_at_target hN hEven).1
  change (B-1/500000)*M  ≤  S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S at hmass
  have hpaid := mul_le_mul_of_nonneg_left hmass hc0
  have hcoefM := mul_le_mul_of_nonneg_right hcoef hM0
  have hcM := mul_le_mul_of_nonneg_right hc6 hM0
  have hremM : QuarterTruncation.truncatedRemainderBound S 4000000 D (preSieveTruncation N)  ≤  (6e-12:ℝ)*M := by
    have hh := mul_le_mul_of_nonneg_right (half_le_liuSingularSeries N)
      (show 0  ≤  (6e-12:ℝ)*((N:ℝ)/log (N:ℝ)^2) by positivity)
    dsimp only [M]
    simp only [div_eq_mul_inv] at hrem hh ⊢
    nlinarith only [hrem,hh]
  have hcount : (A-63/1000)*M  ≤  S.siftedSum := by
    change S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c-
      QuarterTruncation.truncatedRemainderBound S 4000000 D (preSieveTruncation N)  ≤  S.siftedSum at hfinite
    nlinarith only [hfinite,hpaid,hcoefM,hcM,hremM,hM0]
  rw [jurkatRichertSourceBoundingSieve_siftedSum_eq_card N] at hcount
  exact hcount

#print axioms base_candidates_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenPrimeIntervals -/
/-! Sharp reciprocal-prime intervals at the endpoints used by Chen.
The existing Dusart producer is already applicable here at H <= 30. -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LiuWeight PrimeReciprocalLogScale
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem lower_prime_parameters_of_log {N : ℕ} (hL : (130690:ℝ) ≤ log (N:ℝ)) :
    9 ≤ N ∧ (130690:ℝ) ≤ log (N:ℝ) ∧
      (logPowerCutoff 2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) ∧
      (logPowerCutoff 2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) := by
  have hn : 0<N := by
    by_contra h
    have he : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hh := log_le_sub_one_of_pos hnR
  have hn9 : 9 ≤ N := by exact_mod_cast (by linarith only [hL,hh] : (9:ℝ) ≤ N)
  have hroot : (logPowerCutoff 2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) := by
    simp only [logPowerCutoff,Nat.cast_pow,Nat.cast_ofNat]
    apply (log_le_log_iff (by positivity) (rpow_pos_of_pos hnR _)).mp
    rw [log_pow,log_rpow hnR]
    have hl3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,Nat.reducePow,Nat.reduceMul]
    linarith only [hL,hl3]
  exact ⟨hn9,hL,hroot,hroot⟩

theorem lower_prime_prefix_of_log {N : ℕ} (hL : (130690:ℝ) ≤ log (N:ℝ))
    {a : ℝ} (ha : 1/10 ≤ a) :
    |MertensTheorem.primeReciprocalSum (rpowFloor N a)-
      (log a+log (log (N:ℝ))+mertensSecondConstant)| ≤ (1/2)/log (N:ℝ)^2 := by
  have hn9 := (lower_prime_parameters_of_log hL).1
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have ha0 : 0<a := by linarith only [ha]
  have hx : (3:ℝ)^120 ≤ (N:ℝ)^a := by
    apply (log_le_log_iff (by positivity) (rpow_pos_of_pos hn _)).mp
    rw [log_pow,log_rpow hn]
    have hla := mul_le_mul_of_nonneg_right ha hl.le
    have hl3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num only [Nat.cast_ofNat]
    linarith only [hL,hla,hl3]
  have hlogx : 1000≤ log ((N:ℝ)^a) := by
    rw [log_rpow hn]
    have hh := mul_le_mul_of_nonneg_right ha hl.le
    linarith only [hh,hL]
  have hh := sharp_mertens_large hx hlogx
  rw [log_rpow hn,log_mul ha0.ne' hl.ne'] at hh
  rw [MertensTheorem.primeReciprocalSum_eq_analyticNumberTheory,rpowFloor]
  apply hh.trans
  apply (div_le_div_iff₀ (by positivity : 0<10000*(a*log (N:ℝ))^2) (sq_pos_of_pos hl)).mpr
  have hla := mul_le_mul_of_nonneg_right ha hl.le
  have hs := pow_le_pow_left₀ (show 0 ≤ log (N:ℝ)/10 by positivity)
    (show log (N:ℝ)/10 ≤ a*log (N:ℝ) by linarith only [hla]) 2
  nlinarith only [hs]

theorem lower_prime_interval_of_log {N : ℕ} (hL : (130690:ℝ) ≤ log (N:ℝ))
    {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (_hb : b ≤ 1) :
    primeReciprocalLogInterval N a b ≤ log (b/a)+1/log (N:ℝ)^2 := by
  have hn9 := (lower_prime_parameters_of_log hL).1
  have hpa := lower_prime_prefix_of_log hL ha
  have hpb := lower_prime_prefix_of_log hL (ha.trans hab)
  rw [primeReciprocalLogInterval_eq_sub N (by omega) hab,
    log_div (by linarith only [ha,hab] : b≠0) (by linarith only [ha] : a≠0)]
  simp only [div_eq_mul_inv] at hpa hpb ⊢
  linarith only [(abs_le.mp hpa).1,(abs_le.mp hpb).2]

#print axioms lower_prime_interval_of_log
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenMediumPrimeSum -/
section
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
def primePairThreshold : ℕ := targetCutoff

theorem numerical_prime_pair_parameters {N : ℕ} (hN : primePairThreshold  ≤  N) :
    9  ≤  N ∧ (130690:ℝ) ≤ log (N:ℝ) ∧
      (logPowerCutoff 2:ℝ)  ≤  (N:ℝ)^(1/10:ℝ) ∧
      (logPowerCutoff 2:ℝ)  ≤  (N:ℝ)^(1/10:ℝ) :=
  lower_prime_parameters_of_log (by have h := target_log_lower hN; linarith only [h])

theorem numerical_prime_pair_interval {N : ℕ} (hN : primePairThreshold  ≤  N)
    {a b : ℝ} (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1) :
    PrimeReciprocalLogScale.primeReciprocalLogInterval N a b  ≤
      log (b/a)+1/log (N:ℝ)^2 :=
  lower_prime_interval_of_log (numerical_prime_pair_parameters hN).2.1 ha hab hb


theorem numerical_prime_interval_carrier (N : ℕ) (a b : ℝ) :
    (Finset.Ioc (MertensTheorem.rpowFloor N a) (MertensTheorem.rpowFloor N b)).filter Nat.Prime =
      (Finset.range (PrimeReciprocalLogScale.rpowFloor N b+1)).filter
        (fun p : ℕ => p.Prime ∧ (N : ℝ)^a < (p : ℝ) ∧ (p : ℝ)  ≤  (N : ℝ)^b) := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_range,Nat.lt_succ_iff,MertensTheorem.rpowFloor,
    PrimeReciprocalLogScale.rpowFloor,Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) a),
    Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) b)]
  tauto

theorem numerical_medium_profile_integrable {a b : ℝ} (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1/3) :
    IntervalIntegrable (fun x => mediumPrimeProfile x/x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply (show ContinuousOn mediumPrimeProfile (Icc (1/10 : ℝ) (1/3)) from
      jurkatRichertUpperLinearSieveFactor_zeroEpsilon_continuousOn).mono
    intro x hx
    exact ⟨ha.trans hx.1,hx.2.trans hb⟩
  · exact continuousOn_id
  · intro x hx
    linarith only [ha,hx.1]

/-- A quantitative one-dimensional logarithmic Darboux cell. -/
theorem numerical_medium_prime_cell {N : ℕ} (hN : primePairThreshold  ≤  N) {a b : ℝ}
    (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1/3) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b  ≤
      (∫ x in a..b, mediumPrimeProfile x/x)+3600*(b-a)^2+
        192*(1/Real.log (N : ℝ)^2) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := ha0.trans_le hab
  let h := b-a
  let e := 1/Real.log (N : ℝ)^2
  have hh0 : 0  ≤  h := sub_nonneg.mpr hab
  have hh1 : h  ≤  1 := by dsimp [h]; linarith only [ha,hb]
  have he0 : 0  ≤  e := by dsimp [e]; positivity
  obtain ⟨hf0,hf12,_⟩ := numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha,hab.trans hb⟩
  have htest : MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b  ≤
      (mediumPrimeProfile a+180*h)*PrimeReciprocalLogScale.primeReciprocalLogInterval N a b := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
    rw [← numerical_prime_interval_carrier,Finset.mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpc,hprime⟩ := mem_filter.mp hp
    obtain ⟨hpa,hpb⟩ := MertensTheorem.mem_Ioc_rpowFloor_iff.mp hpc
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have halog := Real.log_le_log (Real.rpow_pos_of_pos hN0 a) hpa.le
    have hblog := Real.log_le_log hp0 hpb
    rw [Real.log_rpow hN0] at halog hblog
    have hpinterval : Real.log (p : ℝ)/Real.log (N : ℝ) ∈ Icc a b :=
      ⟨(le_div_iff₀ hL).mpr (by nlinarith only [halog]),(div_le_iff₀ hL).mpr hblog⟩
    have hdiff := (numerical_medium_profile
      ⟨ha.trans hpinterval.1,hpinterval.2.trans hb⟩ ⟨ha,hab.trans hb⟩).2.2
    have habs : |Real.log (p : ℝ)/Real.log (N : ℝ)-a|  ≤  h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hpinterval.1)]
      dsimp [h]
      linarith only [hpinterval.2]
    have hf : mediumPrimeProfile (Real.log (p : ℝ)/Real.log (N : ℝ))  ≤  mediumPrimeProfile a+180*h := by
      have h := (le_abs_self _).trans hdiff
      linarith only [h,habs]
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hf hp0.le
  have hmass := numerical_prime_pair_interval hN ha hab (by linarith only [hb] : b  ≤  1)
  have htest' := htest.trans (mul_le_mul_of_nonneg_left hmass (show 0  ≤  mediumPrimeProfile a+180*h by positivity))
  have hlog0 : 0  ≤  Real.log (b/a) := Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using hab))
  have hlog10 : Real.log (b/a)  ≤  10*h := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have heq : b/a-1 = h/a := by dsimp [h]; field_simp
    apply hh.trans
    rw [heq]
    apply (div_le_iff₀ ha0).mpr
    nlinarith only [ha,mul_nonneg hh0 (sub_nonneg.mpr ha)]
  have hone : IntervalIntegrable (fun x : ℝ => 1/x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id (by intro x hx; linarith only [ha,hx.1])
  have hIntegral : (mediumPrimeProfile a-180*h)*Real.log (b/a)  ≤  ∫ x in a..b, mediumPrimeProfile x/x := by
    have hc := intervalIntegral.integral_mono_on hab (hone.const_mul (mediumPrimeProfile a-180*h))
      (numerical_medium_profile_integrable ha hab hb) (fun x hx => ?_)
    · rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos ha0 hb0] at hc
      exact hc
    · have hdiff := (numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha.trans hx.1,hx.2.trans hb⟩).2.2
      have habs : |a-x|  ≤  h := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx.1)]
        dsimp [h]
        linarith only [hx.2]
      have hf : mediumPrimeProfile a-180*h  ≤  mediumPrimeProfile x := by
        have hh := (le_abs_self _).trans hdiff
        linarith only [hh,habs]
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hf (show 0  ≤  x by linarith only [ha,hx.1])
  have hmesh := mul_le_mul_of_nonneg_left hlog10 (show 0  ≤  360*h by positivity)
  have he := mul_le_mul_of_nonneg_right (show mediumPrimeProfile a+180*h  ≤  192 by linarith only [hf12,hh1]) he0
  change _  ≤  _+3600*h^2+192*e
  change _  ≤  (mediumPrimeProfile a+180*h)*(Real.log (b/a)+e) at htest'
  nlinarith only [htest',hIntegral,hmesh,he]

def mediumPrimeGridPoint (n i : ℕ) : ℝ := 1/10+(7/30 : ℝ)*(i : ℝ)/n

theorem mediumPrimeGridPoint_mono {n : ℕ} (hn : 0 < n) : Monotone (mediumPrimeGridPoint n) := by
  intro i j hij
  unfold mediumPrimeGridPoint
  gcongr

theorem weightedPrimeLogSum_add {N : ℕ} {a b c : ℝ} (hN : 1  ≤  N) (hab : a  ≤  b) (hbc : b  ≤  c) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b+
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N b c =
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a c := by
  unfold MertensTheorem.weightedPrimeReciprocalLogSum
  simp only [Finset.sum_filter]
  apply Finset.sum_Ioc_consecutive
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hbc)

theorem numerical_medium_grid_partition {N n : ℕ} (hN : 1  ≤  N) (hn : 0 < n) (k : ℕ) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
      (mediumPrimeGridPoint n 0) (mediumPrimeGridPoint n k) =
        ∑ i ∈ range k, MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
          (mediumPrimeGridPoint n i) (mediumPrimeGridPoint n (i+1)) := by
  induction k with
  | zero => simp [MertensTheorem.weightedPrimeReciprocalLogSum]
  | succ k ih =>
    rw [Finset.sum_range_succ,← ih]
    exact (weightedPrimeLogSum_add hN (mediumPrimeGridPoint_mono hn (Nat.zero_le k))
      (mediumPrimeGridPoint_mono hn (Nat.le_succ k))).symm

#print axioms numerical_medium_prime_cell
end ChenEffective.GRHQuarterChen

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalMediumPrimeSum.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-effective/NumericalMediumPrimeSum.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.GRHQuarterChen. -/

noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

def mediumPrimeIntegral : ℝ := ∫ a in (1/10 : ℝ)..(1/3 : ℝ), mediumPrimeProfile a/a

theorem numerical_medium_integral_caps : 0  ≤  mediumPrimeIntegral ∧ mediumPrimeIntegral  ≤  120 := by
  have hf (a : ℝ) (ha : a ∈ Icc (1/10 : ℝ) (1/3)) :
      0  ≤  mediumPrimeProfile a/a ∧ mediumPrimeProfile a/a  ≤  120 := by
    have hh := numerical_medium_profile ha ha
    have ha0 : 0 < a := by linarith only [ha.1]
    exact ⟨div_nonneg hh.1 ha0.le,(div_le_iff₀ ha0).mpr (by linarith only [hh.2.1,ha.1])⟩
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun a ha => (hf a ha).1)
  · unfold mediumPrimeIntegral
    calc
      _  ≤  ∫ _a in (1/10 : ℝ)..(1/3 : ℝ), (120 : ℝ) := intervalIntegral.integral_mono_on
        (by norm_num) (numerical_medium_profile_integrable (by norm_num) (by norm_num) (by norm_num))
        intervalIntegrable_const (fun a ha => (hf a ha).2)
      _  ≤  120 := by norm_num

theorem numerical_medium_integral_coefficient :
    jurkatRichertMertensFactor*mediumPrimeIntegral = jurkatRichertQ1MainCoefficient jurkatRichertK := by
  have hh : mediumPrimeIntegral = 2*Real.exp Real.eulerMascheroniConstant/5*(Real.log 8+jurkatRichertK/2) :=
    jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  rw [hh]
  unfold jurkatRichertMertensFactor jurkatRichertQ1MainCoefficient
  have he : Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant=1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  calc
    _ = 8*(Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant)*(Real.log 8+jurkatRichertK/2) := by ring
    _ = _ := by rw [he, mul_one]

theorem numerical_medium_prime_grid {N n : ℕ} (hN : primePairThreshold  ≤  N) (hn : 0 < n) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)  ≤
      mediumPrimeIntegral+196/(n : ℝ)+192*(n : ℝ)*(1/Real.log (N : ℝ)^2) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  let c := mediumPrimeGridPoint n
  let h : ℝ := (7/30 : ℝ)/n
  let e : ℝ := 1/Real.log (N : ℝ)^2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstart : c 0 = 1/10 := by simp [c,mediumPrimeGridPoint]
  have hend : c n = 1/3 := by dsimp [c,mediumPrimeGridPoint]; field_simp; ring
  have hmono : Monotone c := mediumPrimeGridPoint_mono hn
  have hc (i : ℕ) (hi : i  ≤  n) : c i ∈ Icc (1/10 : ℝ) (1/3) := by
    have h1 := hmono (Nat.zero_le i)
    have h2 := hmono hi
    rw [hstart] at h1
    rw [hend] at h2
    exact ⟨h1,h2⟩
  have hstep (i : ℕ) : c (i+1)-c i=h := by dsimp [c,h,mediumPrimeGridPoint]; push_cast; ring
  have hint (i : ℕ) (hi : i < n) : IntervalIntegrable (fun a => mediumPrimeProfile a/a) volume (c i) (c (i+1)) :=
    numerical_medium_profile_integrable (hc i (by omega)).1 (hmono (by omega)) (hc (i+1) (by omega)).2
  have hsum := Finset.sum_le_sum (s := range n) (fun i hi =>
    numerical_medium_prime_cell hN (hc i (by have h := mem_range.mp hi; omega)).1
      (hmono (by omega)) (hc (i+1) (by have h := mem_range.mp hi; omega)).2)
  have hpartition := numerical_medium_grid_partition (N := N) (by omega : 1  ≤  N) hn n
  have hI := intervalIntegral.sum_integral_adjacent_intervals hint
  change (∑ i ∈ range n, ∫ x in c i..c (i+1), mediumPrimeProfile x/x) = _ at hI
  rw [hstart,hend] at hI
  change _ = mediumPrimeIntegral at hI
  change MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (c 0) (c n) = _ at hpartition
  rw [hstart,hend] at hpartition
  rw [← hpartition] at hsum
  simp only [hstep,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  rw [hI] at hsum
  have heq : (n : ℝ)*(3600*h^2)=196/(n : ℝ) := by dsimp [h]; field_simp; ring
  simpa only [heq,mul_assoc,mul_left_comm,e] using hsum

theorem numerical_medium_prime_unshifted {N : ℕ} (hN : primePairThreshold  ≤  N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)  ≤
      mediumPrimeIntegral+13/2000 := by
  have hh := numerical_medium_prime_grid (n := 65000) hN (by norm_num)
  have hL := (numerical_prime_pair_parameters hN).2.1
  have hl : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)  ≤  130690) hL 2
  have he : (192:ℝ)*65000*(1/log (N:ℝ)^2)  ≤  13/4000 := by
    rw [show (192:ℝ)*65000*(1/log (N:ℝ)^2) = (192*65000*1)/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    linarith only [hs]
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,he]

#print axioms numerical_medium_prime_unshifted
end ChenEffective.GRHQuarterChen
end
end

/- Component: GRHQuarterChenMediumKernelCertificates -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def mediumCellStart (i : Fin 64) : ℝ := 1/10+(7/1920:ℝ)*i.val
def mediumCellRatio (i : Fin 64) : ℝ := 5-10*(mediumCellStart i+7/1920)-(89/1000:ℝ)
def mediumKernelCell (i : Fin 64) : ℝ := (7/1920:ℝ)/(mediumCellStart i*(mediumCellRatio i)^2)
def mediumExpPolynomial (u : ℝ) : ℝ := 1+u+u^2/2+u^3/6+u^4/24+u^5/120+u^6/720
def mediumHatEnvelope (s : ℝ) : ℝ :=
  if s ≤ 2 then 1 else if s ≤ 3 then 1/mediumExpPolynomial (s-2) else (3/s)/mediumExpPolynomial (s-2)
def mediumHatCell (i : Fin 64) : ℝ := (7/1920:ℝ)*mediumHatEnvelope (mediumCellRatio i)/mediumCellStart i
def mediumKernelCaps : Fin 64 → ℕ := ![242862,238792,235123,231821,228856,226200,223832,221731,219880,218264,216868,215682,214695,213899,213284,212846,212577,212474,212531,212747,213117,213640,214315,215141,216117,217244,218522,219953,221539,223282,225184,227250,229483,231887,234469,237232,240185,243333,246684,250248,254033,258049,262308,266822,271603,276668,282030,287709,293722,300089,306835,313983,321560,329596,338123,347177,356797,367027,377915,389513,401880,415082,429191,444289]
def mediumHatCaps : Fin 64 → ℕ := ![434500,438770,443682,449219,455371,462129,469490,477451,486015,495187,504974,515384,526431,538129,550492,563539,577292,591771,607002,623011,639827,657481,676006,695440,715710,728115,741006,754392,768281,782681,797603,813058,829055,845608,862727,880427,898722,917624,937151,957316,978137,999631,1021816,1044710,1068332,1092703,1117842,1143772,1170515,1198093,1226532,1255855,1258994,1243341,1228072,1213173,1198632,1184435,1170570,1157026,1143792,1130858,1118212,1105847]

theorem medium_kernel_cell_certificate (i : Fin 64) :
    mediumKernelCell i  ≤  (mediumKernelCaps i:ℝ)/100000000 := by
  fin_cases i <;> norm_num [mediumKernelCell,mediumCellStart,mediumCellRatio,mediumKernelCaps]

theorem medium_hat_cell_certificate (i : Fin 64) :
    mediumHatCell i  ≤  (mediumHatCaps i:ℝ)/100000000 := by
  fin_cases i <;> norm_num [mediumHatCell,mediumCellStart,mediumCellRatio,
    mediumHatEnvelope,mediumExpPolynomial,mediumHatCaps]

theorem medium_kernel_grid_certificate : (∑ i : Fin 64, mediumKernelCell i)  ≤  (169/1000:ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 64))) => medium_kernel_cell_certificate i)
  apply hh.trans
  norm_num [mediumKernelCaps,Fin.sum_univ_succ]

theorem medium_hat_grid_certificate : (∑ i : Fin 64, mediumHatCell i)  ≤  (537/1000:ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 64))) => medium_hat_cell_certificate i)
  apply hh.trans
  norm_num [mediumHatCaps,Fin.sum_univ_succ]

#print axioms medium_kernel_grid_certificate
#print axioms medium_hat_grid_certificate
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenMediumFactor -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem upper_aux_mono {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 4) :
    upperFactorAux s ≤ upperFactorAux t := by
  have hmax : max (3:ℝ) s ≤ max 3 t := max_le_max_left _ hst
  exact (sub_nonneg.mp (numerical_inner_increment (le_max_left _ _) hmax (max_le (by norm_num) ht)).1)

theorem upper_factor_shift {s t : ℝ} (hs : (3/2:ℝ)≤ s) (hst : s≤ t) (ht : t≤4) :
    jurkatRichertMertensFactor*(jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t) ≤40*(t-s)/(s*t) :=
  GRHJoint.upper_factor_shift hs hst ht

theorem upper_factor_window {s t : ℝ} (hs : (3/2:ℝ) ≤ s) (hst : s ≤ t) (ht : t ≤ 4)
    (hshift : t-s ≤ 89/1000) :
    jurkatRichertMertensFactor*
      (jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t) ≤ (89/25:ℝ)/(t-89/1000)^2 := by
  have hs0 : 0<s := by linarith only [hs]
  have ht0 : 0<t := hs0.trans_le hst
  have hden0 : 0<t-89/1000 := by linarith only [hs,hst]
  have hden : (t-89/1000)^2 ≤ s*t := by
    have ha : 0 ≤ s-(t-89/1000) := by linarith only [hshift]
    have hb : 0 ≤ t-(t-89/1000) := by norm_num
    nlinarith only [mul_nonneg ha ht0.le,mul_nonneg hb hden0.le]
  apply (upper_factor_shift hs hst ht).trans
  apply (div_le_div_iff₀ (mul_pos hs0 ht0) (sq_pos_of_pos hden0)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hshift (sq_nonneg (t-89/1000)),hden]

theorem medium_exp_polynomial_bounds {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ mediumExpPolynomial u ∧ mediumExpPolynomial u ≤ exp u := by
  constructor
  · unfold mediumExpPolynomial
    have hh : 0 ≤ u+u^2/2+u^3/6+u^4/24+u^5/120+u^6/720 := by positivity
    linarith only [hh]
  · have hh := sum_le_exp_of_nonneg hu 7
    norm_num [Finset.sum_range_succ] at hh
    convert hh using 1 <;> unfold mediumExpPolynomial <;> ring

theorem medium_hat_envelope_bound {s : ℝ} (hs : (3/2:ℝ) ≤ s) :
    exp 2*sieveHat s ≤ mediumHatEnvelope s := by
  have hs0 : 0<s := by linarith only [hs]
  unfold mediumHatEnvelope
  by_cases hs2 : s ≤ 2
  · rw [if_pos hs2]
    unfold sieveHat
    rw [if_pos hs2,← exp_add]
    norm_num
  · rw [if_neg hs2]
    have hu : 0 ≤ s-2 := by linarith only [hs2]
    have hp := medium_exp_polynomial_bounds hu
    have hrec : 1/exp (s-2) ≤ 1/mediumExpPolynomial (s-2) :=
      one_div_le_one_div_of_le (by linarith only [hp.1]) hp.2
    have heq : exp 2*exp (-s)=1/exp (s-2) := by
      rw [← exp_add,one_div,← exp_neg]
      congr 1
      ring
    by_cases hs3 : s ≤ 3
    · rw [if_pos hs3]
      unfold sieveHat
      rw [if_neg hs2,if_pos hs3,heq]
      exact hrec
    · rw [if_neg hs3]
      unfold sieveHat
      rw [if_neg hs2,if_neg hs3]
      have hh := mul_le_mul_of_nonneg_left hrec
        (show 0 ≤ (3:ℝ)/s by positivity)
      calc
        _ = (3/s)*(exp 2*exp (-s)) := by ring
        _ = (3/s)*(1/exp (s-2)) := by rw [heq]
        _ ≤ (3/s)*(1/mediumExpPolynomial (s-2)) := hh
        _ = _ := by ring

#print axioms upper_factor_window
#print axioms medium_hat_envelope_bound
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenMediumGrid -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

def mediumGridNat (i : ℕ) : ℝ := 1/10+(7/1920:ℝ)*i

theorem medium_grid_mono : Monotone mediumGridNat := by
  intro i j hij
  unfold mediumGridNat
  gcongr

theorem weighted_log_add (f : ℝ → ℝ) {N : ℕ} {a b c : ℝ}
    (hN : 1 ≤ N) (hab : a ≤ b) (hbc : b ≤ c) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N a b+
      MertensTheorem.weightedPrimeReciprocalLogSum f N b c=
      MertensTheorem.weightedPrimeReciprocalLogSum f N a c := by
  unfold MertensTheorem.weightedPrimeReciprocalLogSum
  simp only [sum_filter]
  apply sum_Ioc_consecutive
  · exact Nat.floor_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
  · exact Nat.floor_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hbc)

theorem medium_grid_partition (f : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N (mediumGridNat 0) (mediumGridNat n)=
      ∑ i : Fin n, MertensTheorem.weightedPrimeReciprocalLogSum f N
        (mediumGridNat i.val) (mediumGridNat (i.val+1)) := by
  induction n with
  | zero => simp [MertensTheorem.weightedPrimeReciprocalLogSum]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [← ih]
    exact (weighted_log_add f hN (medium_grid_mono (Nat.zero_le n))
      (medium_grid_mono (Nat.le_succ n))).symm

theorem medium_darboux_cell (f : ℝ → ℝ) {N : ℕ} (hN : targetCutoff ≤ N)
    {a b U : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3)
    (hU : 0 ≤ U) (hf : ∀ x ∈ Icc a b, f x ≤ U) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N a b ≤ U*((b-a)/a+1/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hLp : 0<log (N:ℝ) := by linarith only [hL]
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := (numerical_prime_pair_parameters hN).1; omega)
  have ha0 : 0<a := by linarith only [ha]
  have hb0 : 0<b := ha0.trans_le hab
  have htest : MertensTheorem.weightedPrimeReciprocalLogSum f N a b ≤ U*PrimeReciprocalLogScale.primeReciprocalLogInterval N a b := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
    rw [← numerical_prime_interval_carrier,mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpc,hprime⟩ := mem_filter.mp hp
    obtain ⟨hpa,hpb⟩ := MertensTheorem.mem_Ioc_rpowFloor_iff.mp hpc
    have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
    have halog := log_le_log (rpow_pos_of_pos hNp a) hpa.le
    have hblog := log_le_log hp0 hpb
    rw [log_rpow hNp] at halog hblog
    have hx : log (p:ℝ)/log (N:ℝ)∈Icc a b :=
      ⟨(le_div_iff₀ hLp).mpr (by nlinarith only [halog]),(div_le_iff₀ hLp).mpr hblog⟩
    simpa only [mul_one_div] using div_le_div_of_nonneg_right (hf _ hx) hp0.le
  have hm := numerical_prime_pair_interval hN ha hab (by linarith only [hb])
  have hl : log (b/a) ≤ (b-a)/a := by
    have hh := log_le_sub_one_of_pos (div_pos hb0 ha0)
    convert hh using 1 <;> field_simp <;> ring
  exact htest.trans (mul_le_mul_of_nonneg_left (hm.trans (add_le_add hl le_rfl)) hU)

theorem medium_darboux_grid (f : ℝ → ℝ) {N : ℕ} (hN : targetCutoff ≤ N)
    (U : Fin 64 → ℝ) (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1)
    (hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → f x ≤ U i) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N (1/10) (1/3) ≤ (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i))+64*(1/log (N:ℝ)^2) := by
  have hN1 : 1 ≤ N := by have := (numerical_prime_pair_parameters hN).1; omega
  have hsum := Finset.sum_le_sum (fun i (_ : i∈(univ : Finset (Fin 64))) =>
    medium_darboux_cell f hN (a:=mediumCellStart i) (b:=mediumCellStart i+7/1920)
      (by unfold mediumCellStart; have hi := Nat.cast_nonneg (α:=ℝ) i.val; linarith only [hi])
      (by linarith)
      (by
        have hi : (i.val:ℝ) ≤ 63 := by exact_mod_cast (show i.val ≤ 63 by omega)
        unfold mediumCellStart
        linarith only [hi])
      (hU i).1 (hf i))
  have hp := medium_grid_partition f hN1 64
  have hc0 : mediumGridNat 0=(1/10:ℝ) := by norm_num [mediumGridNat]
  have hc64 : mediumGridNat 64=(1/3:ℝ) := by norm_num [mediumGridNat]
  rw [hc0,hc64] at hp
  have heq (i : Fin 64) : mediumGridNat i.val=mediumCellStart i ∧
      mediumGridNat (i.val+1)=mediumCellStart i+7/1920 := by
    constructor
    · rfl
    · unfold mediumGridNat mediumCellStart
      push_cast
      ring
  simp_rw [(heq _).1,(heq _).2] at hp
  rw [← hp] at hsum
  have hmass : (∑ i : Fin 64, U i) ≤ 64 := by
    have hh := sum_le_sum (fun i (_ : i∈(univ : Finset (Fin 64))) => (hU i).2)
    simpa using hh
  have hh := mul_le_mul_of_nonneg_right hmass (show 0 ≤ 1/log (N:ℝ)^2 by positivity)
  have hsplit : (∑ i : Fin 64, U i*((mediumCellStart i+7/1920-mediumCellStart i)/mediumCellStart i+
      1/log (N:ℝ)^2)) =
      (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i))+
        (∑ i : Fin 64, U i)*(1/log (N:ℝ)^2) := by
    rw [sum_mul,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsplit] at hsum
  linarith only [hsum,hh]

def mediumKernelProfile (a : ℝ) : ℝ := 1/(5-10*a-(89/1000:ℝ))^2
def mediumHatProfile (a : ℝ) : ℝ := exp 2*sieveHat (5-10*a-(89/1000:ℝ))

theorem medium_cell_ratio_lower (i : Fin 64) : (3/2:ℝ) ≤ mediumCellRatio i := by
  have hi : (i.val:ℝ) ≤ 63 := by exact_mod_cast (show i.val ≤ 63 by omega)
  unfold mediumCellRatio mediumCellStart
  linarith only [hi]

theorem medium_kernel_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumKernelProfile N (1/10) (1/3) ≤ (17/100:ℝ) := by
  let U := fun i : Fin 64 => 1/(mediumCellRatio i)^2
  have hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1 := by
    intro i
    have hs := medium_cell_ratio_lower i
    dsimp only [U]
    constructor
    · positivity
    · apply (div_le_iff₀ (by nlinarith only [hs] : 0<(mediumCellRatio i)^2)).mpr
      nlinarith only [hs,sq_nonneg (mediumCellRatio i-1)]
  have hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → mediumKernelProfile x ≤ U i := by
    intro i x hx
    have hs := medium_cell_ratio_lower i
    have hle : mediumCellRatio i ≤ 5-10*x-(89/1000:ℝ) := by unfold mediumCellRatio; linarith only [hx.2]
    apply one_div_le_one_div_of_le (by nlinarith only [hs] : 0<(mediumCellRatio i)^2)
    exact pow_le_pow_left₀ (by linarith only [hs]) hle 2
  have hh := medium_darboux_grid mediumKernelProfile hN U hU hf
  have hc : (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i)) ≤ (169/1000:ℝ) := by
    convert medium_kernel_grid_certificate using 1
    apply sum_congr rfl
    intro i _
    dsimp only [U,mediumKernelCell]
    ring
  have hL := target_log_lower hN
  have he : 64*(1/log (N:ℝ)^2) ≤ (1/1000000:ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 130690) hL 2
    rw [show 64*(1/log (N:ℝ)^2)=64/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (by nlinarith only [hL] : 0<log (N:ℝ)^2)).mpr
    nlinarith only [hp]
  linarith only [hh,hc,he]

theorem medium_hat_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumHatProfile N (1/10) (1/3) ≤ (27/50:ℝ) := by
  let U := fun i : Fin 64 => exp 2*sieveHat (mediumCellRatio i)
  have hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1 := by
    intro i
    constructor
    · exact mul_nonneg (exp_pos 2).le (sieveHat_pos _).le
    · exact sieveHat_normalized_le_one _
  have hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → mediumHatProfile x ≤ U i := by
    intro i x hx
    have hle : mediumCellRatio i ≤ 5-10*x-(89/1000:ℝ) := by unfold mediumCellRatio; linarith only [hx.2]
    exact mul_le_mul_of_nonneg_left (sieveHat_antitone hle) (exp_pos 2).le
  have hh := medium_darboux_grid mediumHatProfile hN U hU hf
  have hc : (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i)) ≤ (537/1000:ℝ) := by
    apply le_trans _ medium_hat_grid_certificate
    apply sum_le_sum
    intro i _
    have ha : 0 ≤ (7/1920:ℝ)/mediumCellStart i := by unfold mediumCellStart; positivity
    have hp := mul_le_mul_of_nonneg_right
      (medium_hat_envelope_bound (medium_cell_ratio_lower i)) ha
    dsimp only [U,mediumHatCell]
    convert hp using 1 <;> ring
  have hL := target_log_lower hN
  have he : 64*(1/log (N:ℝ)^2) ≤ (1/1000000:ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 130690) hL 2
    rw [show 64*(1/log (N:ℝ)^2)=64/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (by nlinarith only [hL] : 0<log (N:ℝ)^2)).mpr
    nlinarith only [hp]
  linarith only [hh,hc,he]

#print axioms medium_kernel_prime_sum
#print axioms medium_hat_prime_sum
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenMediumIntegralCaps -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem medium_K_bounds : 0 ≤ jurkatRichertK ∧ jurkatRichertK ≤ (5/8:ℝ) := by
  have hpoint (u : ℝ) (hu : u∈Icc (3:ℝ) 4) :
      0 ≤ 10/(u*(5-u))*jurkatRichertInnerIntegral u ∧
      10/(u*(5-u))*jurkatRichertInnerIntegral u ≤ (5/8:ℝ) := by
    have hd : (4:ℝ) ≤ u*(5-u) := by
      nlinarith only [hu.1,hu.2,mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)]
    have hp := inner_integral_quarter hu.1 hu.2
    have hr : (10:ℝ)/(u*(5-u)) ≤ 5/2 :=
      (div_le_iff₀ (by linarith only [hd])).mpr (by linarith only [hd])
    constructor
    · exact mul_nonneg (by positivity) hp.1
    · exact (mul_le_mul hr hp.2 hp.1 (by norm_num)).trans (by norm_num)
  have hc : ContinuousOn (fun u : ℝ => 10/(u*(5-u))*jurkatRichertInnerIntegral u) (Icc 3 4) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      intro u hu
      have hu0 : 0<u := by linarith only [hu.1]
      have hu5 : 0<5-u := by linarith only [hu.2]
      exact (mul_pos hu0 hu5).ne'
    · apply continuousOn_jurkatRichertInnerIntegral_three_five.mono
      intro u hu
      exact ⟨hu.1,hu.2.trans (by norm_num)⟩
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (by norm_num : (3:ℝ) ≤ 4) hc
  unfold jurkatRichertK
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun u hu => (hpoint u hu).1)
  · calc
      _ ≤ ∫ _u in (3:ℝ)..4, (5/8:ℝ) := intervalIntegral.integral_mono_on
        (by norm_num) hi intervalIntegrable_const (fun u hu => (hpoint u hu).2)
      _ = _ := by norm_num

theorem medium_integral_small_cap : 0 ≤ mediumPrimeIntegral ∧ mediumPrimeIntegral ≤ 3 := by
  have hI0 := numerical_medium_integral_caps.1
  have hK := medium_K_bounds
  have hlog0 : 0 ≤ log (8:ℝ) := log_nonneg (by norm_num)
  have hlog : log (8:ℝ) ≤ 21/10 := by
    rw [show (8:ℝ)=2^3 by norm_num,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_lt_d9]
  have hE : exp eulerMascheroniConstant ≤ 3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have heq : mediumPrimeIntegral=(2*exp eulerMascheroniConstant/5)*(log 8+jurkatRichertK/2) :=
    jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  refine ⟨hI0,?_⟩
  rw [heq]
  apply (mul_le_mul (show 2*exp eulerMascheroniConstant/5 ≤ (6/5:ℝ) by linarith only [hE])
    (show log 8+jurkatRichertK/2 ≤ (5/2:ℝ) by linarith only [hlog,hK.2])
    (show 0 ≤ log 8+jurkatRichertK/2 by linarith only [hlog0,hK.1]) (by norm_num)).trans
  norm_num

#print axioms medium_integral_small_cap
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenMediumProfile -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

def mediumUpperProfile (a : ℝ) : ℝ :=
  (jurkatRichertMertensFactor+21/1000)*mediumPrimeProfile a+
    (9087/2500:ℝ)*mediumKernelProfile a+(6887/10000:ℝ)*mediumHatProfile a

theorem medium_pointwise_budget {a s : ℝ} (ha : a∈Icc (1/10:ℝ) (1/3))
    (hs : (3/2:ℝ) ≤ s) (hst : s ≤ 5-10*a) (hshift : 5-10*a-s ≤ 89/1000) :
    (jurkatRichertMertensFactor+21/1000)*
      (jurkatRichertUpperLinearSieveFactor s+110*(1/2000:ℝ)*exp 2*sieveHat s) ≤ mediumUpperProfile a := by
  let B := jurkatRichertMertensFactor
  let X := jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor (5-10*a)
  have hBmin : (1:ℝ) ≤ B := mertens_factor_lower_one
  have hBpos : 0 ≤ B := by linarith only [hBmin]
  have hK : 0 ≤ mediumKernelProfile a := by unfold mediumKernelProfile; positivity
  have hstep : B*X ≤ (89/25:ℝ)*mediumKernelProfile a := by
    have hh := upper_factor_window hs hst (show 5-10*a ≤ (4:ℝ) by linarith only [ha.1]) hshift
    convert hh using 1 <;> dsimp only [B,X,mediumKernelProfile] <;> ring
  have hX : (B+21/1000)*X ≤ (9087/2500:ℝ)*mediumKernelProfile a := by
    by_cases hx : 0 ≤ X
    · have hh := mul_le_mul_of_nonneg_right hBmin hx
      have hh' := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 1021/1000)
      nlinarith only [hh,hh',hstep,hK]
    · have hx' : X ≤ 0 := le_of_not_ge hx
      have hh := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ B+21/1000 by linarith only [hBpos]) hx'
      nlinarith only [hh,hK]
  have hHat : exp 2*sieveHat s ≤ mediumHatProfile a := by
    unfold mediumHatProfile
    apply mul_le_mul_of_nonneg_left _ (exp_pos 2).le
    apply sieveHat_antitone
    linarith only [hshift]
  have hHat0 : 0 ≤ exp 2*sieveHat s := mul_nonneg (exp_pos 2).le (sieveHat_pos s).le
  have hHatScaled := mul_le_mul
    (show B+21/1000 ≤ (12521/1000:ℝ) by have := budget_mertens_factor_cap; dsimp only [B]; linarith)
    hHat hHat0 (by norm_num : (0:ℝ) ≤ 12521/1000)
  unfold mediumUpperProfile mediumPrimeProfile
  dsimp only [X,B] at *
  nlinarith only [hX,hHatScaled,hHat0,hHat]

theorem medium_profile_nonneg {a : ℝ} (ha : a∈Icc (1/10:ℝ) (1/3)) :
    0 ≤ mediumUpperProfile a := by
  have hf := (numerical_medium_profile ha ha).1
  have hB : 0 ≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hk : 0 ≤ mediumKernelProfile a := by unfold mediumKernelProfile; positivity
  have hh : 0 ≤ mediumHatProfile a := mul_nonneg (exp_pos 2).le (sieveHat_pos _).le
  unfold mediumUpperProfile
  positivity

theorem medium_profile_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+(1137/1000:ℝ) := by
  let B := jurkatRichertMertensFactor
  have hBpos : 0 ≤ B := by dsimp only [B]; unfold jurkatRichertMertensFactor; positivity
  have hbase := mul_le_mul_of_nonneg_left (numerical_medium_prime_unshifted hN)
    (show 0 ≤ B+21/1000 by linarith only [hBpos])
  have hk := mul_le_mul_of_nonneg_left (medium_kernel_prime_sum hN) (by norm_num : (0:ℝ) ≤ 9087/2500)
  have hh := mul_le_mul_of_nonneg_left (medium_hat_prime_sum hN) (by norm_num : (0:ℝ) ≤ 6887/10000)
  have heq : MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) =
      (B+21/1000)*MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)+
      (9087/2500:ℝ)*MertensTheorem.weightedPrimeReciprocalLogSum mediumKernelProfile N (1/10) (1/3)+
      (6887/10000:ℝ)*MertensTheorem.weightedPrimeReciprocalLogSum mediumHatProfile N (1/10) (1/3) := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    rw [mul_sum,mul_sum,mul_sum,← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    dsimp only [mediumUpperProfile,B]
    ring
  have hI := medium_integral_small_cap.2
  have hBc : B ≤ (25/2:ℝ) := budget_mertens_factor_cap
  have hmain := numerical_medium_integral_coefficient
  rw [heq]
  dsimp only [B] at *
  nlinarith only [hbase,hk,hh,hI,hBc,hmain]

theorem medium_prime_large {N q : ℕ} (hN : targetCutoff ≤ N)
    (hq : q∈jurkatRichertSourceMediumPrimes N) : 1000001 ≤ q := by
  have hr := (numerical_prime_pair_parameters hN).2.2.1
  have hc : (1000000:ℝ) ≤ (logPowerCutoff 2:ℝ) := by
    exact_mod_cast (show (1000000:ℕ) ≤ logPowerCutoff 2 by unfold logPowerCutoff; norm_num)
  have hqLower := (mem_filter.mp hq).2.2.1
  have hh : (1000000:ℝ)<q := (hc.trans hr).trans_lt hqLower
  exact_mod_cast hh

theorem medium_profile_source_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1)) ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+(1138/1000:ℝ) := by
  have hN9 := (numerical_prime_pair_parameters hN).1
  have hN1 : 1 ≤ N := by have := (numerical_prime_pair_parameters hN).1; omega
  have hsum : (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/(q:ℝ)) =
      MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) := by
    rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor hN1]
    rfl
  have hpoint : ∀ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1) ≤ (1+1/1000000:ℝ)*(mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/(q:ℝ)) := by
    intro q hq
    have hqBig : (1000001:ℝ) ≤ q := by exact_mod_cast medium_prime_large hN hq
    have hq0 : (0:ℝ)<q := by linarith only [hqBig]
    have hqm : 0<(q:ℝ)-1 := by linarith only [hqBig]
    have hf := medium_profile_nonneg (jurkatRichertSourceMediumPrime_log_mem (by omega : 1<N) hq)
    have hr : (1:ℝ)/((q:ℝ)-1) ≤ (1+1/1000000:ℝ)/(q:ℝ) :=
      (div_le_div_iff₀ hqm hq0).mpr (by nlinarith only [hqBig])
    have hh := mul_le_mul_of_nonneg_left hr hf
    convert hh using 1 <;> ring
  have hh := sum_le_sum hpoint
  rw [← mul_sum,hsum] at hh
  have hp := mul_le_mul_of_nonneg_left (medium_profile_prime_sum hN)
    (by norm_num : (0:ℝ) ≤ 1+1/1000000)
  have hQ : jurkatRichertQ1MainCoefficient jurkatRichertK ≤ (75/2:ℝ) := by
    rw [← numerical_medium_integral_coefficient]
    exact (mul_le_mul budget_mertens_factor_cap medium_integral_small_cap.2
      medium_integral_small_cap.1 (by norm_num)).trans (by norm_num)
  linarith only [hh,hp,hQ]

#print axioms medium_profile_source_sum
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenMediumAggregate -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem conditioned_sifted_upper {N q : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hq : q∈jurkatRichertSourceMediumPrimes N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum ≤ (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2)*
        (mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1))+
      QuarterTruncation.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q)
        4000000 (lowerLevel N q) (preSieveTruncation N) := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let S₀ := jurkatRichertSourceBoundingSieve N
  let s := lowerRatio N q
  let D := lowerLevel N q
  let Z := Nat.ceil ((D:ℝ)^(1/s))
  let c := jurkatRichertUpperLinearSieveFactor s+110*(1/2000:ℝ)*exp 2*sieveHat s
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let B := jurkatRichertMertensFactor
  have hNbig := (lower_endpoint_parameters hN).1
  have hqp := (mem_filter.mp hq).2.1
  have hq0 : (0:ℝ)<q := by exact_mod_cast hqp.pos
  have hqm : 0<(q:ℝ)-1 := by
    have hh : (1:ℝ)<q := by exact_mod_cast hqp.one_lt
    linarith only [hh]
  have hs := lower_medium_ratio hN hq
  obtain ⟨hD,hZD,hroot,hlevel⟩ := lower_level_geometry hN hqp.pos hs.1
  have hcut : ∀ p∈(preSieveCounting S 4000000).prodPrimes.primeFactors, p<Z := by
    intro p hp
    change p∈(restrictSievePrimes S 4000000).prodPrimes.primeFactors at hp
    rw [restrictSievePrimes_primeFactors] at hp
    have hh := jurkatRichertSourceConditioned_primeFactor_le_cutoff N q p (mem_filter.mp hp).1
    exact Nat.lt_ceil.mpr (hh.trans_lt hroot)
  have hmass0 : 0 ≤ S.totalMass := div_nonneg
    (LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2) (by positivity)
      (by exact_mod_cast (show 2 ≤ N by omega))) hqm.le
  have hf := QuarterTruncation.truncated_preSieveCounting_upper_bound S 4000000 hmass0
    (by norm_num : (0:ℝ) ≤ 1/4000) le_rfl (lower_conditioned_relative N q)
    D Z (preSieveTruncation N) (truncation_log_lower hN).1 hD hs.1 hs.2 rfl hZD hcut
  have hc0 : 0 ≤ c := by
    have hh := (numerical_upper_factor_regular ⟨by linarith only [hs.1],hs.2⟩
      ⟨by linarith only [hs.1],hs.2⟩).1
    have hp : 0 ≤ 110*(1/2000:ℝ)*exp 2*sieveHat s := mul_nonneg (by positivity) (sieveHat_pos s).le
    dsimp only [c]
    linarith only [hh,hp]
  have hmass := (source_mass_at_target hN hEven).2
  change S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀ ≤ (B+21/1000)*M at hmass
  have hcond : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤ (B+21/1000)*M/((q:ℝ)-1) := by
    have heq : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S =
        (S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀)/((q:ℝ)-1) := by
      change ((S₀.totalMass/((q:ℝ)-1))*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀) =
        (S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀)/((q:ℝ)-1)
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hmass hqm.le
  have hm := mul_le_mul_of_nonneg_right hcond hc0
  have ha := jurkatRichertSourceMediumPrime_log_mem (by omega : 1<N) hq
  have hshift := lower_ratio_shift hN hqp.pos
  have hp := medium_pointwise_budget ha hs.1 (by linarith only [hshift.1]) hshift.2
  change (B+21/1000)*c ≤ mediumUpperProfile (log (q:ℝ)/log (N:ℝ)) at hp
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hM0) hqm.le
  have hm' : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c ≤ M*(mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1)) := by
    apply hm.trans
    convert hh using 1 <;> ring
  change S.siftedSum ≤ S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c+
    QuarterTruncation.truncatedRemainderBound S 4000000 D (preSieveTruncation N) at hf
  exact hf.trans (add_le_add hm' le_rfl)

theorem medium_aggregate_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceMediumPrimeAggregate N ≤ (jurkatRichertQ1MainCoefficient jurkatRichertK+(1139/1000:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let D := lowerLevel N
  let R := fun q => QuarterTruncation.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q)
    4000000 (D q) (preSieveTruncation N)
  have hD : ∀ q∈jurkatRichertSourceMediumPrimes N, 1 ≤ D q := by
    intro q hq
    have hh := (lower_level_geometry hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1).1
    change 1 < D q at hh
    omega
  have hDN : ∀ q∈jurkatRichertSourceMediumPrimes N, D q ≤ N := fun q hq =>
    lower_level_le_endpoint hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1
  have hlevel : ∀ q∈jurkatRichertSourceMediumPrimes N,
      preSieveTruncation N*D q ≤ jurkatRichertSourceUpperLevel N q (9/2500:ℝ) := fun q hq =>
    lower_level_in_source hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1
  have hr := medium_truncated_remainders hN hEven D hD hDN hlevel
  change (∑ q∈jurkatRichertSourceMediumPrimes N, R q) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 at hr
  have hs := sum_le_sum (fun q (_ : q∈jurkatRichertSourceMediumPrimes N) =>
    conditioned_sifted_upper hN hEven ‹q∈jurkatRichertSourceMediumPrimes N›)
  have heq : (∑ q∈jurkatRichertSourceMediumPrimes N,
      (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum)=jurkatRichertSourceMediumPrimeAggregate N := by
    unfold jurkatRichertSourceMediumPrimeAggregate
    apply sum_congr rfl
    intro q _
    exact jurkatRichertSourceConditionedBoundingSieve_siftedSum_eq_card N q
  rw [heq,sum_add_distrib,← mul_sum] at hs
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hp := mul_le_mul_of_nonneg_left (medium_profile_source_sum hN) hM0
  have hrM : (∑ q∈jurkatRichertSourceMediumPrimes N, R q) ≤ (6e-12:ℝ)*M := by
    have hh := mul_le_mul_of_nonneg_right (half_le_liuSingularSeries N)
      (show 0 ≤ (6e-12:ℝ)*((N:ℝ)/log (N:ℝ)^2) by positivity)
    dsimp only [M]
    simp only [div_eq_mul_inv] at hr hh ⊢
    nlinarith only [hr,hh]
  change jurkatRichertSourceMediumPrimeAggregate N ≤ _
  change jurkatRichertSourceMediumPrimeAggregate N ≤ M*(∑ q∈jurkatRichertSourceMediumPrimes N, mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1))+
      ∑ q∈jurkatRichertSourceMediumPrimes N, R q at hs
  nlinarith only [hs,hp,hrM,hM0]

#print axioms medium_aggregate_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenWeightedLower -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real
open MathlibNt.SieveTheory SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem endpoint_payment_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    60*(N:ℝ)^(9/10:ℝ) ≤ (1/20000:ℝ)*
      (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := (lower_endpoint_parameters hN).1; omega)
  have hp := truncated_polynomial_payment hL (A:=(60:ℝ)) (by norm_num)
    (α:=(1/10:ℝ)) (by norm_num) (k:=2) (by norm_num)
  have hid : (N:ℝ)^(9/10:ℝ)=(N:ℝ)*exp (-(1/10:ℝ)*log (N:ℝ)) := by
    calc
      _ = exp (log (N:ℝ)*(9/10:ℝ)) := rpow_def_of_pos hn _
      _ = exp (log (N:ℝ))*exp (-(1/10:ℝ)*log (N:ℝ)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = _ := by rw [exp_log hn]
  have hfirst : 60*(N:ℝ)^(9/10:ℝ) ≤ (1e-6:ℝ)*((N:ℝ)/log (N:ℝ)^2) := by
    calc
      _ = ((60:ℝ)*(log (N:ℝ))^2*exp (-(1/10:ℝ)*log (N:ℝ)))*
          ((N:ℝ)/log (N:ℝ)^2) := by rw [hid]; field_simp [hl.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have hs := half_le_liuSingularSeries N
  have hc : (1e-6:ℝ) ≤ (1/20000:ℝ)*SingularSeries.liuSingularSeries N := by linarith only [hs]
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (N:ℝ)/log (N:ℝ)^2 by positivity)
  apply hfirst.trans
  convert hh using 1 <;> ring

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem source_boundary_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceWeightedCount N ≤ jurkatRichertWeightedCount N+
      (1/20000:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hsmall : (2:ℕ)^110+1 ≤ 3^100 := by norm_num
  have hpower : (3:ℕ)^100 ≤ targetCutoff := by
    rw [targetCutoff_eq]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hbig : (2:ℕ)^110<N := by have hh := hsmall.trans (hpower.trans hN); omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N hbig hEven
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le N hbig hEven
  have he := endpoint_payment_at_target hN
  have hn : 0 ≤ (N:ℝ)^(9/10:ℝ) := rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith only [hb,hp,he,hn]

theorem weighted_lower_of_window {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    (2.00825:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N := by
  let b : ChenBudget := ⟨63/1000,1139/1000,1/20000,0,0⟩
  have hh := chen_budget_weighted b (base_candidates_at_target hN hEven)
    (medium_aggregate_at_target hN hEven) (source_boundary_at_target hN hEven)
  convert hh using 1
  norm_num [b,ChenBudget.weighted]

#print axioms weighted_lower_of_window
end ChenEffective.GRHQuarterChen
end

