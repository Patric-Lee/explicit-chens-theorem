import BJSReciprocalIntervalBridge

/-! A sufficient, explicit theta-error target for the actual pre-sieve endpoint.
The theta estimate is a theorem hypothesis, not an axiom or a claimed result.
Unlike the existing contour bound, this target would suffice at 3^120.
-/
noncomputable section
namespace ChenEffective
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem bjsStudy_mertens_of_theta_target {x : ℝ} (hx : 9 ≤ x)
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t-t| ≤ (3/4)*t^(15/16 : ℝ)) :
    |primeReciprocalSum ⌊x⌋₊-(log (log x)+mertensSecondConstant)| ≤
      (3/4)*(17*log x+16)/(log x)^2*x^(-1/16 : ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hl : 0 < log x := log_pos (by linarith only [hx])
  have hk (t : ℝ) (ht : x ≤ t) :
      ‖thetaErrorKernel t‖ ≤ (3/4)*((log x+1)/(log x)^2)*t^(-17/16 : ℝ) := by
    have ht0 : 0 < t := hx0.trans_le ht
    have hlog : log x ≤ log t := log_le_log hx0 ht
    have hlt : 0 < log t := hl.trans_le hlog
    have hi := one_div_le_one_div_of_le hl hlog
    have hi2 := one_div_le_one_div_of_le (sq_pos_of_pos hl)
      (show (log x)^2 ≤ (log t)^2 by nlinarith only [hl,hlog])
    have hr : (log t+1)/(log t)^2 ≤ (log x+1)/(log x)^2 := by
      have htx : (log t+1)/(log t)^2=1/log t+1/(log t)^2 := by field_simp
      have hxx : (log x+1)/(log x)^2=1/log x+1/(log x)^2 := by field_simp
      rw [htx,hxx]
      exact add_le_add hi hi2
    have hnorm : ‖thetaErrorKernel t‖ =
        |Chebyshev.theta t-t| *((log t+1)/(t*log t)^2) := by
      unfold thetaErrorKernel
      rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (by linarith only [hlt] : 0 ≤ log t+1),
        abs_of_nonneg (sq_nonneg (t*log t))]
      ring
    have heq : t^(15/16 : ℝ)/t^2=t^(-17/16 : ℝ) := by
      rw [← rpow_two,← rpow_sub ht0]
      norm_num
    rw [hnorm]
    calc
      _ ≤ ((3/4)*t^(15/16 : ℝ))*((log t+1)/(t*log t)^2) :=
        mul_le_mul_of_nonneg_right (hθ t ht) (by positivity)
      _ = (3/4)*((log t+1)/(log t)^2)*(t^(15/16 : ℝ)/t^2) := by field_simp
      _ ≤ (3/4)*((log x+1)/(log x)^2)*t^(-17/16 : ℝ) := by
        rw [heq]
        gcongr
  have hint := integrableOn_Ioi_rpow_of_lt (by norm_num : (-17/16 : ℝ) < -1) hx0
  have htail : ‖∫ t in Ioi x, thetaErrorKernel t‖ ≤
      12*((log x+1)/(log x)^2)*x^(-1/16 : ℝ) := by
    calc
      _ ≤ ∫ t in Ioi x, (3/4)*((log x+1)/(log x)^2)*t^(-17/16 : ℝ) := by
        apply norm_integral_le_of_norm_le (hint.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hk t ht.le
      _ = _ := by
        rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hx0]
        norm_num
        ring
  have hend : |(Chebyshev.theta x-x)/(x*log x)| ≤
      (3/4)/log x*x^(-1/16 : ℝ) := by
    rw [abs_div,abs_of_pos (mul_pos hx0 hl)]
    calc
      _ ≤ ((3/4)*x^(15/16 : ℝ))/(x*log x) :=
        div_le_div_of_nonneg_right (hθ x le_rfl) (by positivity)
      _ = (3/4)/log x*(x^(15/16 : ℝ)/x^(1 : ℝ)) := by rw [rpow_one]; field_simp
      _ = _ := by rw [← rpow_sub hx0]; norm_num
  rw [mertensSecond_error_decomposition (by linarith only [hx])]
  have hh := abs_sub ((Chebyshev.theta x-x)/(x*log x)) (∫ t in Ioi x, thetaErrorKernel t)
  rw [Real.norm_eq_abs] at htail
  have heq : (3/4)/log x*x^(-1/16 : ℝ)+12*((log x+1)/(log x)^2)*x^(-1/16 : ℝ)=
      (3/4)*(17*log x+16)/(log x)^2*x^(-1/16 : ℝ) := by field_simp; ring
  exact hh.trans (by rw [← heq]; exact add_le_add hend htail)

theorem bjsStudy_theta_target_payment {a : ℝ} (ha : 0 < a) (hlog : 131 ≤ log a) :
    (3/4)*(17*log a+16)/(log a)^2*a^(-1/16 : ℝ) ≤ 1/(2*(log a)^2) := by
  let L := log a
  have hL : 131 ≤ L := hlog
  have hL0 : 0 < L := by linarith only [hL]
  have hnum : (3/4 : ℝ)*(34*131+32) ≤ exp (131/16 : ℝ) := by
    have he : (2718/1000 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718/1000) he 8
    rw [← exp_nat_mul] at hp
    have ht := add_one_le_exp (3/16 : ℝ)
    have hh := mul_le_mul hp ht (by norm_num : (0 : ℝ) ≤ 3/16+1) (exp_pos _).le
    rw [← exp_add] at hh
    norm_num at hh ⊢
    linarith only [hh]
  have ht := add_one_le_exp ((L-131)/16)
  have hlin : (3/4 : ℝ)*(34*L+32) ≤ (3/4)*(34*131+32)*exp ((L-131)/16) := by
    nlinarith only [hL,ht]
  have hpay : (3/4 : ℝ)*(34*L+32)*exp (-L/16) ≤ 1 := by
    calc
      _ ≤ ((3/4)*(34*131+32)*exp ((L-131)/16))*exp (-L/16) :=
        mul_le_mul_of_nonneg_right hlin (exp_pos _).le
      _ = ((3/4)*(34*131+32))*exp (-131/16 : ℝ) := by
        rw [mul_assoc,← exp_add]
        congr 2
        ring
      _ ≤ exp (131/16 : ℝ)*exp (-131/16 : ℝ) :=
        mul_le_mul_of_nonneg_right hnum (exp_pos _).le
      _ = 1 := by rw [← exp_add]; norm_num
  have hr : a^(-1/16 : ℝ)=exp (-L/16) := by
    rw [rpow_def_of_pos ha]
    congr 1
    dsimp [L]
    ring
  rw [hr]
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hL0) (by positivity : 0 < 2*L^2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hpay (sq_nonneg L)]

theorem bjsStudy_prefix_at_presieve_of_theta_target {x : ℝ}
    (hx : (3 : ℝ)^(120 : ℕ) ≤ x)
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t-t| ≤ (3/4)*t^(15/16 : ℝ)) :
    |primeReciprocalSum ⌊x⌋₊-(log (log x)+mertensSecondConstant)| ≤ 1/(2*(log x)^2) := by
  have hx0 : 0 < x := (pow_pos (by norm_num : (0 : ℝ) < 3) 120).trans_le hx
  have hthree : (131/120 : ℝ) ≤ log 3 := by
    have hh := sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1) 3
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hh := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 3) 120) hx
  rw [log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hlog : 131 ≤ log x := by linarith only [hh,hthree]
  have hx9 : 9 ≤ x := by linarith only [hlog,log_le_sub_one_of_pos hx0]
  exact (bjsStudy_mertens_of_theta_target hx9 hθ).trans (bjsStudy_theta_target_payment hx0 hlog)

#print axioms bjsStudy_prefix_at_presieve_of_theta_target

/-- At a composite integer endpoint the inclusive prefix is disjoint from
the requested prime interval. This handles the exact pre-sieve endpoint. -/
theorem bjsStudy_interval_prefix_composite (s : Finset ℕ) (n : ℕ) (b : ℝ)
    (hn : ¬n.Prime) (hab : (n : ℝ) ≤ b)
    (hs : ∀ p ∈ s, p.Prime ∧ (n : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p ∈ s, 1/(p : ℝ))+primeReciprocalSum n ≤ primeReciprocalSum ⌊b⌋₊ := by
  have hsubS : s ⊆ primesUpTo ⌊b⌋₊ := by
    intro p hp
    exact mem_primesUpTo.mpr ⟨(hs p hp).1,Nat.le_floor (hs p hp).2.2⟩
  have hsubP : primesUpTo n ⊆ primesUpTo ⌊b⌋₊ := primesUpTo_mono (Nat.le_floor hab)
  have hdis : Disjoint s (primesUpTo n) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpn
    have hpge : n ≤ p := by exact_mod_cast (hs p hp).2.1
    have heq : p=n := le_antisymm (mem_primesUpTo.mp hpn).2 hpge
    exact hn (heq ▸ (hs p hp).1)
  unfold primeReciprocalSum
  rw [← Finset.sum_union hdis]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hsubS hsubP)
    (fun p _ _ => by positivity)

/-- Only the range from 3^120 upward is needed to replace the interval
input consumed by the pre-sieved product proof. The theta hypothesis is
still an open analytic obligation, not an asserted theorem. -/
theorem bjsStudy_presieve_interval_of_theta_target
    (hθ : ∀ t : ℝ, (3 : ℝ)^(120 : ℕ) ≤ t →
      |Chebyshev.theta t-t| ≤ (3/4)*t^(15/16 : ℝ))
    (s : Finset ℕ) (a b : ℝ) (ha : (3 : ℝ)^(120 : ℕ) ≤ a) (hab : a ≤ b)
    (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p ∈ s, 1/(p : ℝ)) ≤ log (log b/log a)+1/(log a)^2 := by
  have hstart : (1 : ℝ) < (3 : ℝ)^(120 : ℕ) := by norm_num
  have ha1 : 1 < a := hstart.trans_le ha
  have ha0 : 0 < a := by linarith only [ha1]
  have hla : 0 < log a := log_pos ha1
  have hlb : 0 < log b := log_pos (ha1.trans_le hab)
  have hP (x : ℝ) (hx : (3 : ℝ)^(120 : ℕ) ≤ x) :=
    bjsStudy_prefix_at_presieve_of_theta_target hx (fun t ht => hθ t (hx.trans ht))
  have hU : primeReciprocalSum ⌊b⌋₊ ≤ log (log b)+mertensSecondConstant+1/(2*(log b)^2) := by
    linarith only [(abs_le.mp (hP b (ha.trans hab))).2]
  have hh : (∑ p ∈ s, 1/(p : ℝ)) ≤
      (log (log b)+mertensSecondConstant+1/(2*(log b)^2))-
        (log (log a)+mertensSecondConstant-1/(2*(log a)^2)) := by
    rcases lt_or_eq_of_le ha with hstrict | heq
    · have hL : ∀ x : ℝ, (3 : ℝ)^(120 : ℕ) < x →
          log (log x)+mertensSecondConstant-1/(2*(log x)^2) ≤ primeReciprocalSum ⌊x⌋₊ := by
        intro x hx
        linarith only [(abs_le.mp (hP x hx.le)).1]
      have hc : ContinuousAt (fun x : ℝ => log (log x)+mertensSecondConstant-1/(2*(log x)^2)) a := by
        fun_prop (disch := positivity)
      exact bjsStudy_interval_of_prefix (a := a) (b := b) (t := (3 : ℝ)^(120 : ℕ))
        (L := fun x : ℝ => log (log x)+mertensSecondConstant-1/(2*(log x)^2)) s
        (by positivity) hstrict hab hs hL hU hc
    · have han : ((3^120 : ℕ) : ℝ)=a := by exact_mod_cast heq
      have hd := bjsStudy_interval_prefix_composite s (3^120) b
        (Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 120)) (han ▸ hab) (han ▸ hs)
      have hfloor : ⌊a⌋₊=3^120 := by rw [← han]; exact Nat.floor_natCast _
      have hL := (abs_le.mp (hP a ha)).1
      rw [hfloor] at hL
      linarith only [hd,hL,hU]
  have hlog : log a ≤ log b := log_le_log ha0 hab
  have he : 1/(2*(log b)^2) ≤ 1/(2*(log a)^2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith only [hlog,hla,hlb])
  rw [log_div hlb.ne' hla.ne']
  have hid : 2*(1/(2*(log a)^2))=1/(log a)^2 := by ring
  linarith only [hh,he,hid]

#print axioms bjsStudy_presieve_interval_of_theta_target
end ChenEffective
