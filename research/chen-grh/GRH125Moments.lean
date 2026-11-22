import AuditGRHStrongMoving

/-! Finer cumulative-theta moments, with no prime enumeration.
Each interval is processed separately; no exponentially branching partition
proof or untrusted numerical result is used. -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def rootPrefix (F : Finset ℕ) (x : ℕ) : ℝ := ∑ p ∈ F.filter (fun p => p≤ x), 1/sqrt (p:ℝ)
def thetaPrefix (F : Finset ℕ) (x : ℕ) : ℝ := ∑ p ∈ F.filter (fun p => p≤ x), log (p:ℝ)

theorem theta_prefix_nonneg (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) (x : ℕ) :
    0≤ thetaPrefix F x := by
  exact sum_nonneg (fun p hp => log_nonneg (by exact_mod_cast (hF p (mem_filter.mp hp).1).one_lt.le))

theorem theta_prefix_cap (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) (x : ℕ) :
    thetaPrefix F x≤(7/5:ℝ)*x := by
  have hh := ChenEffective.presieve_log_cost (F.filter (fun p => p≤ x)) (Nat.cast_nonneg (α:=ℝ) x)
    (fun p hp => ⟨hF p (mem_filter.mp hp).1,by exact_mod_cast (mem_filter.mp hp).2⟩)
  rw [log_prod (fun p hp => by exact_mod_cast (hF p (mem_filter.mp hp).1).ne_zero)] at hh
  have hc : log (4:ℝ)≤7/5 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α:=ℝ) x)
  exact hh.trans hm

theorem root_prefix_small (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    rootPrefix F 100≤20 := by
  have hh := GRH.reciprocal_sqrt_subset (F.filter (fun p => p≤100)) 100
    (by intro p hp; exact ⟨(hF p (mem_filter.mp hp).1).one_lt.le,(mem_filter.mp hp).2⟩)
  norm_num at hh
  simpa only [rootPrefix,one_div] using hh

theorem root_prefix_step (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    (a b : ℕ) (ell c C v : ℝ) (ha : 0<a) (hab : a≤ b) (hell : 0<ell)
    (hlog : ell≤ log (a:ℝ)) (hvw : v≤1/(ell*sqrt (a:ℝ)))
    (hprev : rootPrefix F a≤ c+(1/(ell*sqrt (a:ℝ)))*thetaPrefix F a)
    (hcost : c+(1/(ell*sqrt (a:ℝ))-v)*((7/5:ℝ)*b)≤ C) :
    rootPrefix F b≤ C+v*thetaPrefix F b := by
  have hi := GRHSub13.prime_root_interval_difference F hF a b ell ha hab hell hlog
  have hsplit : rootPrefix F b = rootPrefix F a+
      (∑ p ∈ F.filter (fun p => a<p ∧ p≤ b), 1/sqrt (p:ℝ)) := by
    simp only [rootPrefix,sum_filter]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> first | omega | ring
  change _≤(thetaPrefix F b-thetaPrefix F a)/(ell*sqrt (a:ℝ)) at hi
  have hm := mul_le_mul_of_nonneg_left (theta_prefix_cap F hF b) (sub_nonneg.mpr hvw)
  rw [show (thetaPrefix F b-thetaPrefix F a)/(ell*sqrt (a:ℝ))=
    (1/(ell*sqrt (a:ℝ)))*(thetaPrefix F b-thetaPrefix F a) by ring] at hi
  nlinarith only [hi,hsplit,hm,hprev,hcost]

theorem prime_root_moment (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ p≤4000000) :
    (∑ p ∈ F, 1/sqrt (p:ℝ))≤500 := by
  classical
  have hprime : ∀ p ∈ F, p.Prime := fun p hp => (hF p hp).1
  have hsmall := root_prefix_small F hprime
  have hnonneg := theta_prefix_nonneg F hprime 100
  have h0 : rootPrefix F 100≤20+(50/2079:ℝ)*thetaPrefix F 100 := by
    nlinarith only [hsmall,hnonneg]
  have h1 : rootPrefix F 121≤(25463/1250:ℝ)+(500/22869:ℝ)*thetaPrefix F 121 := by
    apply root_prefix_step F hprime 100 121 (6*693/1000) (20:ℝ) (25463/1250:ℝ) (500/22869:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 6 100 (6*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h0 using 1 <;> norm_num
    · norm_num
  have h2 : rootPrefix F 169≤(54479/2500:ℝ)+(1000/63063:ℝ)*thetaPrefix F 169 := by
    apply root_prefix_step F hprime 121 169 (6*693/1000) (25463/1250:ℝ) (54479/2500:ℝ) (1000/63063:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 6 121 (6*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h1 using 1 <;> norm_num
    · norm_num
  have h3 : rootPrefix F 225≤(224577/10000:ℝ)+(200/14553:ℝ)*thetaPrefix F 225 := by
    apply root_prefix_step F hprime 169 225 (7*693/1000) (54479/2500:ℝ) (224577/10000:ℝ) (200/14553:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 7 169 (7*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h2 using 1 <;> norm_num
    · norm_num
  have h4 : rootPrefix F 289≤(59313/2500:ℝ)+(125/11781:ℝ)*thetaPrefix F 289 := by
    apply root_prefix_step F hprime 225 289 (7*693/1000) (224577/10000:ℝ) (59313/2500:ℝ) (125/11781:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 7 225 (7*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h3 using 1 <;> norm_num
    · norm_num
  have h5 : rootPrefix F 361≤(242897/10000:ℝ)+(125/13167:ℝ)*thetaPrefix F 361 := by
    apply root_prefix_step F hprime 289 361 (8*693/1000) (59313/2500:ℝ) (242897/10000:ℝ) (125/13167:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 8 289 (8*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h4 using 1 <;> norm_num
    · norm_num
  have h6 : rootPrefix F 441≤(3106/125:ℝ)+(125/14553:ℝ)*thetaPrefix F 441 := by
    apply root_prefix_step F hprime 361 441 (8*693/1000) (242897/10000:ℝ) (3106/125:ℝ) (125/14553:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 8 361 (8*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h5 using 1 <;> norm_num
    · norm_num
  have h7 : rootPrefix F 576≤(263873/10000:ℝ)+(125/18711:ℝ)*thetaPrefix F 576 := by
    apply root_prefix_step F hprime 441 576 (8*693/1000) (3106/125:ℝ) (263873/10000:ℝ) (125/18711:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 8 441 (8*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h6 using 1 <;> norm_num
    · norm_num
  have h8 : rootPrefix F 729≤(271449/10000:ℝ)+(1000/168399:ℝ)*thetaPrefix F 729 := by
    apply root_prefix_step F hprime 576 729 (9*693/1000) (263873/10000:ℝ) (271449/10000:ℝ) (1000/168399:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 9 576 (9*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h7 using 1 <;> norm_num
    · norm_num
  have h9 : rootPrefix F 900≤(69733/2500:ℝ)+(100/18711:ℝ)*thetaPrefix F 900 := by
    apply root_prefix_step F hprime 729 900 (9*693/1000) (271449/10000:ℝ) (69733/2500:ℝ) (100/18711:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 9 729 (9*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h8 using 1 <;> norm_num
    · norm_num
  have h10 : rootPrefix F 1089≤(293747/10000:ℝ)+(100/22869:ℝ)*thetaPrefix F 1089 := by
    apply root_prefix_step F hprime 900 1089 (9*693/1000) (69733/2500:ℝ) (293747/10000:ℝ) (100/22869:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 9 900 (9*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h9 using 1 <;> norm_num
    · norm_num
  have h11 : rootPrefix F 1369≤(37851/1250:ℝ)+(100/25641:ℝ)*thetaPrefix F 1369 := by
    apply root_prefix_step F hprime 1089 1369 (10*693/1000) (293747/10000:ℝ) (37851/1250:ℝ) (100/25641:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 10 1089 (10*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h10 using 1 <;> norm_num
    · norm_num
  have h12 : rootPrefix F 1681≤(311763/10000:ℝ)+(100/28413:ℝ)*thetaPrefix F 1681 := by
    apply root_prefix_step F hprime 1369 1681 (10*693/1000) (37851/1250:ℝ) (311763/10000:ℝ) (100/28413:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 10 1369 (10*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h11 using 1 <;> norm_num
    · norm_num
  have h13 : rootPrefix F 2116≤(41443/1250:ℝ)+(500/175329:ℝ)*thetaPrefix F 2116 := by
    apply root_prefix_step F hprime 1681 2116 (10*693/1000) (311763/10000:ℝ) (41443/1250:ℝ) (500/175329:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 10 1681 (10*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h12 using 1 <;> norm_num
    · norm_num
  have h14 : rootPrefix F 2601≤(13669/400:ℝ)+(1000/388773:ℝ)*thetaPrefix F 2601 := by
    apply root_prefix_step F hprime 2116 2601 (11*693/1000) (41443/1250:ℝ) (13669/400:ℝ) (1000/388773:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 11 2116 (11*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h13 using 1 <;> norm_num
    · norm_num
  have h15 : rootPrefix F 3249≤(354041/10000:ℝ)+(1000/434511:ℝ)*thetaPrefix F 3249 := by
    apply root_prefix_step F hprime 2601 3249 (11*693/1000) (13669/400:ℝ) (354041/10000:ℝ) (1000/434511:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 11 2601 (11*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h14 using 1 <;> norm_num
    · norm_num
  have h16 : rootPrefix F 3969≤(366221/10000:ℝ)+(1000/480249:ℝ)*thetaPrefix F 3969 := by
    apply root_prefix_step F hprime 3249 3969 (11*693/1000) (354041/10000:ℝ) (366221/10000:ℝ) (1000/480249:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 11 3249 (11*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h15 using 1 <;> norm_num
    · norm_num
  have h17 : rootPrefix F 4900≤(391219/10000:ℝ)+(25/14553:ℝ)*thetaPrefix F 4900 := by
    apply root_prefix_step F hprime 3969 4900 (11*693/1000) (366221/10000:ℝ) (391219/10000:ℝ) (25/14553:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 11 3969 (11*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h16 using 1 <;> norm_num
    · norm_num
  have h18 : rootPrefix F 5929≤(202091/5000:ℝ)+(250/160083:ℝ)*thetaPrefix F 5929 := by
    apply root_prefix_step F hprime 4900 5929 (12*693/1000) (391219/10000:ℝ) (202091/5000:ℝ) (250/160083:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 12 4900 (12*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h17 using 1 <;> norm_num
    · norm_num
  have h19 : rootPrefix F 7225≤(8381/200:ℝ)+(50/35343:ℝ)*thetaPrefix F 7225 := by
    apply root_prefix_step F hprime 5929 7225 (12*693/1000) (202091/5000:ℝ) (8381/200:ℝ) (50/35343:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 12 5929 (12*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h18 using 1 <;> norm_num
    · norm_num
  have h20 : rootPrefix F 8836≤(447979/10000:ℝ)+(500/423423:ℝ)*thetaPrefix F 8836 := by
    apply root_prefix_step F hprime 7225 8836 (12*693/1000) (8381/200:ℝ) (447979/10000:ℝ) (500/423423:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 12 7225 (12*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h19 using 1 <;> norm_num
    · norm_num
  have h21 : rootPrefix F 10816≤(465173/10000:ℝ)+(125/117117:ℝ)*thetaPrefix F 10816 := by
    apply root_prefix_step F hprime 8836 10816 (13*693/1000) (447979/10000:ℝ) (465173/10000:ℝ) (125/117117:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 13 8836 (13*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h20 using 1 <;> norm_num
    · norm_num
  have h22 : rootPrefix F 13225≤(121019/2500:ℝ)+(200/207207:ℝ)*thetaPrefix F 13225 := by
    apply root_prefix_step F hprime 10816 13225 (13*693/1000) (465173/10000:ℝ) (121019/2500:ℝ) (200/207207:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 13 10816 (13*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h21 using 1 <;> norm_num
    · norm_num
  have h23 : rootPrefix F 16129≤(50467/1000:ℝ)+(1000/1144143:ℝ)*thetaPrefix F 16129 := by
    apply root_prefix_step F hprime 13225 16129 (13*693/1000) (121019/2500:ℝ) (50467/1000:ℝ) (1000/1144143:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 13 13225 (13*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h22 using 1 <;> norm_num
    · norm_num
  have h24 : rootPrefix F 19600≤(6781/125:ℝ)+(25/33957:ℝ)*thetaPrefix F 19600 := by
    apply root_prefix_step F hprime 16129 19600 (13*693/1000) (50467/1000:ℝ) (6781/125:ℝ) (25/33957:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 13 16129 (13*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h23 using 1 <;> norm_num
    · norm_num
  have h25 : rootPrefix F 23716≤(564703/10000:ℝ)+(250/373527:ℝ)*thetaPrefix F 23716 := by
    apply root_prefix_step F hprime 19600 23716 (14*693/1000) (6781/125:ℝ) (564703/10000:ℝ) (250/373527:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 14 19600 (14*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h24 using 1 <;> norm_num
    · norm_num
  have h26 : rootPrefix F 28900≤(59019/1000:ℝ)+(50/82467:ℝ)*thetaPrefix F 28900 := by
    apply root_prefix_step F hprime 23716 28900 (14*693/1000) (564703/10000:ℝ) (59019/1000:ℝ) (50/82467:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 14 23716 (14*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h25 using 1 <;> norm_num
    · norm_num
  have h27 : rootPrefix F 35344≤(637/10:ℝ)+(50/97713:ℝ)*thetaPrefix F 35344 := by
    apply root_prefix_step F hprime 28900 35344 (14*693/1000) (59019/1000:ℝ) (637/10:ℝ) (50/97713:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 14 28900 (14*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h26 using 1 <;> norm_num
    · norm_num
  have h28 : rootPrefix F 42849≤(83147/1250:ℝ)+(200/430353:ℝ)*thetaPrefix F 42849 := by
    apply root_prefix_step F hprime 35344 42849 (15*693/1000) (637/10:ℝ) (83147/1250:ℝ) (200/430353:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 15 35344 (15*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h27 using 1 <;> norm_num
    · norm_num
  have h29 : rootPrefix F 51984≤(696329/10000:ℝ)+(50/118503:ℝ)*thetaPrefix F 51984 := by
    apply root_prefix_step F hprime 42849 51984 (15*693/1000) (83147/1250:ℝ) (696329/10000:ℝ) (50/118503:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 15 42849 (15*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h28 using 1 <;> norm_num
    · norm_num
  have h30 : rootPrefix F 63001≤(730431/10000:ℝ)+(200/521829:ℝ)*thetaPrefix F 63001 := by
    apply root_prefix_step F hprime 51984 63001 (15*693/1000) (696329/10000:ℝ) (730431/10000:ℝ) (200/521829:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 15 51984 (15*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h29 using 1 <;> norm_num
    · norm_num
  have h31 : rootPrefix F 76729≤(99049/1250:ℝ)+(125/383922:ℝ)*thetaPrefix F 76729 := by
    apply root_prefix_step F hprime 63001 76729 (15*693/1000) (730431/10000:ℝ) (99049/1250:ℝ) (125/383922:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 15 63001 (15*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h30 using 1 <;> norm_num
    · norm_num
  have h32 : rootPrefix F 93025≤(20783/250:ℝ)+(25/84546:ℝ)*thetaPrefix F 93025 := by
    apply root_prefix_step F hprime 76729 93025 (16*693/1000) (99049/1250:ℝ) (20783/250:ℝ) (25/84546:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 16 76729 (16*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h31 using 1 <;> norm_num
    · norm_num
  have h33 : rootPrefix F 112896≤(21861/250:ℝ)+(125/465696:ℝ)*thetaPrefix F 112896 := by
    apply root_prefix_step F hprime 93025 112896 (16*693/1000) (20783/250:ℝ) (21861/250:ℝ) (125/465696:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 16 93025 (16*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h32 using 1 <;> norm_num
    · norm_num
  have h34 : rootPrefix F 136900≤(189839/2000:ℝ)+(100/435897:ℝ)*thetaPrefix F 136900 := by
    apply root_prefix_step F hprime 112896 136900 (16*693/1000) (21861/250:ℝ) (189839/2000:ℝ) (100/435897:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 16 112896 (16*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h33 using 1 <;> norm_num
    · norm_num
  have h35 : rootPrefix F 166464≤(998991/10000:ℝ)+(125/600831:ℝ)*thetaPrefix F 166464 := by
    apply root_prefix_step F hprime 136900 166464 (17*693/1000) (189839/2000:ℝ) (998991/10000:ℝ) (125/600831:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 17 136900 (17*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h34 using 1 <;> norm_num
    · norm_num
  have h36 : rootPrefix F 201601≤(105261/1000:ℝ)+(1000/5289669:ℝ)*thetaPrefix F 201601 := by
    apply root_prefix_step F hprime 166464 201601 (17*693/1000) (998991/10000:ℝ) (105261/1000:ℝ) (1000/5289669:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 17 166464 (17*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h35 using 1 <;> norm_num
    · norm_num
  have h37 : rootPrefix F 244036≤(555723/5000:ℝ)+(500/2909907:ℝ)*thetaPrefix F 244036 := by
    apply root_prefix_step F hprime 201601 244036 (17*693/1000) (105261/1000:ℝ) (555723/5000:ℝ) (500/2909907:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 17 201601 (17*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h36 using 1 <;> norm_num
    · norm_num
  have h38 : rootPrefix F 295936≤(1212793/10000:ℝ)+(125/848232:ℝ)*thetaPrefix F 295936 := by
    apply root_prefix_step F hprime 244036 295936 (17*693/1000) (555723/5000:ℝ) (1212793/10000:ℝ) (125/848232:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 17 244036 (17*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h37 using 1 <;> norm_num
    · norm_num
  have h39 : rootPrefix F 358801≤(1280763/10000:ℝ)+(500/3735963:ℝ)*thetaPrefix F 358801 := by
    apply root_prefix_step F hprime 295936 358801 (18*693/1000) (1212793/10000:ℝ) (1280763/10000:ℝ) (500/3735963:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 18 295936 (18*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h38 using 1 <;> norm_num
    · norm_num
  have h40 : rootPrefix F 434281≤(1354849/10000:ℝ)+(500/4110183:ℝ)*thetaPrefix F 434281 := by
    apply root_prefix_step F hprime 358801 434281 (18*693/1000) (1280763/10000:ℝ) (1354849/10000:ℝ) (500/4110183:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 18 358801 (18*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h39 using 1 <;> norm_num
    · norm_num
  have h41 : rootPrefix F 525625≤(92448/625:ℝ)+(40/381843:ℝ)*thetaPrefix F 525625 := by
    apply root_prefix_step F hprime 434281 525625 (18*693/1000) (1354849/10000:ℝ) (92448/625:ℝ) (40/381843:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 18 434281 (18*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h40 using 1 <;> norm_num
    · norm_num
  have h42 : rootPrefix F 636804≤(782301/5000:ℝ)+(500/5253633:ℝ)*thetaPrefix F 636804 := by
    apply root_prefix_step F hprime 525625 636804 (19*693/1000) (92448/625:ℝ) (782301/5000:ℝ) (500/5253633:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 19 525625 (19*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h41 using 1 <;> norm_num
    · norm_num
  have h43 : rootPrefix F 770884≤(1658191/10000:ℝ)+(500/5780313:ℝ)*thetaPrefix F 770884 := by
    apply root_prefix_step F hprime 636804 770884 (19*693/1000) (782301/5000:ℝ) (1658191/10000:ℝ) (500/5780313:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 19 636804 (19*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h42 using 1 <;> norm_num
    · norm_num
  have h44 : rootPrefix F 933156≤(1761137/10000:ℝ)+(500/6359661:ℝ)*thetaPrefix F 933156 := by
    apply root_prefix_step F hprime 770884 933156 (19*693/1000) (1658191/10000:ℝ) (1761137/10000:ℝ) (500/6359661:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 19 770884 (19*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h43 using 1 <;> norm_num
    · norm_num
  have h45 : rootPrefix F 1129969≤(1931143/10000:ℝ)+(50/736659:ℝ)*thetaPrefix F 1129969 := by
    apply root_prefix_step F hprime 933156 1129969 (19*693/1000) (1761137/10000:ℝ) (1931143/10000:ℝ) (50/736659:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 19 933156 (19*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h44 using 1 <;> norm_num
    · norm_num
  have h46 : rootPrefix F 1368900≤(256263/1250:ℝ)+(5/81081:ℝ)*thetaPrefix F 1368900 := by
    apply root_prefix_step F hprime 1129969 1368900 (20*693/1000) (1931143/10000:ℝ) (256263/1250:ℝ) (5/81081:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 20 1129969 (20*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h45 using 1 <;> norm_num
    · norm_num
  have h47 : rootPrefix F 1656369≤(272513/1250:ℝ)+(50/891891:ℝ)*thetaPrefix F 1656369 := by
    apply root_prefix_step F hprime 1368900 1656369 (20*693/1000) (256263/1250:ℝ) (272513/1250:ℝ) (50/891891:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 20 1368900 (20*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h46 using 1 <;> norm_num
    · norm_num
  have h48 : rootPrefix F 2005056≤(580867/2500:ℝ)+(25/490644:ℝ)*thetaPrefix F 2005056 := by
    apply root_prefix_step F hprime 1656369 2005056 (20*693/1000) (272513/1250:ℝ) (580867/2500:ℝ) (25/490644:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 20 1656369 (20*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h47 using 1 <;> norm_num
    · norm_num
  have h49 : rootPrefix F 2427364≤(2556227/10000:ℝ)+(500/11336787:ℝ)*thetaPrefix F 2427364 := by
    apply root_prefix_step F hprime 2005056 2427364 (20*693/1000) (580867/2500:ℝ) (2556227/10000:ℝ) (500/11336787:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 20 2005056 (20*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h48 using 1 <;> norm_num
    · norm_num
  have h50 : rootPrefix F 2937796≤(1360663/5000:ℝ)+(500/12471921:ℝ)*thetaPrefix F 2937796 := by
    apply root_prefix_step F hprime 2427364 2937796 (21*693/1000) (2556227/10000:ℝ) (1360663/5000:ℝ) (500/12471921:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 21 2427364 (21*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h49 using 1 <;> norm_num
    · norm_num
  have h51 : rootPrefix F 3556996≤(580679/2000:ℝ)+(500/13723479:ℝ)*thetaPrefix F 3556996 := by
    apply root_prefix_step F hprime 2937796 3556996 (21*693/1000) (1360663/5000:ℝ) (580679/2000:ℝ) (500/13723479:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 21 2937796 (21*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h50 using 1 <;> norm_num
    · norm_num
  have h52 : rootPrefix F 4000000≤(2471847/5000:ℝ)+(0:ℝ)*thetaPrefix F 4000000 := by
    apply root_prefix_step F hprime 3556996 4000000 (21*693/1000) (580679/2000:ℝ) (2471847/5000:ℝ) (0:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (GRH.log_lower_of_two_power 21 3556996 (21*693/1000) (by norm_num) (by norm_num))
      (by norm_num)
    · convert h51 using 1 <;> norm_num
    · norm_num
  have hf : F.filter (fun p => p≤4000000)=F := filter_eq_self.mpr (fun p hp => (hF p hp).2)
  simp only [zero_mul,add_zero,rootPrefix,hf] at h52
  exact h52.trans (by norm_num)

theorem goldbach_root_prime_tight {p : ℕ} (hp : p.Prime) (hp2 : 2<p) :
    sqrt (p:ℝ)*AnalyticNumberTheory.Sieve.goldbachNu p≤
      (101/100:ℝ)/sqrt (p:ℝ)+(if p≤100 then (1/4:ℝ)/sqrt (p:ℝ) else 0)+(if p=3 then 1 else 0) := by
  by_cases hsmall : p≤100
  · have hh := GRH.goldbach_root_prime_bound hp hp2
    simp only [if_pos hsmall]
    have hpos : 0≤1/sqrt (p:ℝ) := by positivity
    ring_nf at hh hpos ⊢
    linarith only [hh,hpos]
  · have hpr : (101:ℝ)≤ p := by exact_mod_cast (show 101≤ p by omega)
    have hs : 0<sqrt (p:ℝ) := sqrt_pos.mpr (by linarith only [hpr])
    have hpm : 0<(p:ℝ)-1 := by linarith only [hpr]
    rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime hp]
    simp only [if_neg hsmall,if_neg (show p≠3 by omega),add_zero,mul_one_div]
    apply (div_le_div_iff₀ hpm hs).mpr
    nlinarith only [sq_sqrt (Nat.cast_nonneg p : (0:ℝ)≤ p),hpr]

open ArithmeticFunction ChenEffective.GRH
theorem reciprocal_divisor_moment_four_million_sharp {Q : ℕ} (hQ : Squarefree Q)
    (hprimes : ∀ p ∈ Q.primeFactors, p ≤ 4000000) :
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 500 := by
  have hh := squarefree_divisor_moment_le_exp hQ inverseRootArithmeticFunction
    inverseRootArithmeticFunction_mult (fun p _ => by
      change 0 ≤ 1/sqrt (p:ℝ)
      positivity)
  change (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤
    exp (∑ p ∈ Q.primeFactors, 1/sqrt (p:ℝ)) at hh
  exact hh.trans (exp_le_exp.mpr (prime_root_moment Q.primeFactors
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,hprimes p hp⟩)))

theorem density_divisor_moment_four_million_sharp {Q : ℕ} (hQ : Squarefree Q)
    (hprimes : ∀ p ∈ Q.primeFactors, p ≤ 4000000)
    (v : ArithmeticFunction ℝ) (hv : v.IsMultiplicative)
    (hpos : ∀ p ∈ Q.primeFactors, 0 ≤ v p)
    (hprime : ∀ p ∈ Q.primeFactors,
      sqrt (p:ℝ)*v p ≤ (101/100:ℝ)/sqrt (p:ℝ)+(if p≤100 then (1/4:ℝ)/sqrt (p:ℝ) else 0)+(if p=3 then 1 else 0)) :
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*v d) ≤ exp 512 := by
  have hh := squarefree_divisor_moment_le_exp hQ
    (rootArithmeticFunction.pmul v) (rootArithmeticFunction_mult.pmul hv)
    (fun p hp => by
      change 0 ≤ sqrt (p:ℝ)*v p
      exact mul_nonneg (sqrt_nonneg _) (hpos p hp))
  change (∑ d ∈ Q.divisors, sqrt (d:ℝ)*v d) ≤
    exp (∑ p ∈ Q.primeFactors, sqrt (p:ℝ)*v p) at hh
  apply hh.trans
  apply exp_le_exp.mpr
  have hroot := prime_root_moment Q.primeFactors
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,hprimes p hp⟩)
  have hsum := sum_le_sum hprime
  have heq : (∑ p ∈ Q.primeFactors, (101/100:ℝ)/sqrt (p:ℝ)) =
      (101/100:ℝ)*(∑ p ∈ Q.primeFactors, 1/sqrt (p:ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  have hind : (∑ p ∈ Q.primeFactors, if p=3 then (1:ℝ) else 0) ≤ 1 := by
    simp only [sum_ite_eq']
    split_ifs <;> norm_num
  have hsmall := root_prefix_small Q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hsmall_eq : (∑ p ∈ Q.primeFactors, if p≤100 then (1/4:ℝ)/sqrt (p:ℝ) else 0)=
      (1/4:ℝ)*rootPrefix Q.primeFactors 100 := by
    simp only [rootPrefix,sum_filter,mul_sum]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> ring
  simp only [sum_add_distrib,heq,hsmall_eq] at hsum
  linarith only [hsum,hroot,hind,hsmall]

theorem source_small_prime_divisor_moments_sharp (N : ℕ) :
    let Q := ChenEffective.smallSievePrimeProduct
      (MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertSourceBoundingSieve N) 4000000
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 500 ∧
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*AnalyticNumberTheory.Sieve.goldbachNu d) ≤ exp 512 := by
  let S := MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertSourceBoundingSieve N
  let Q := ChenEffective.smallSievePrimeProduct S 4000000
  have hQ : Squarefree Q :=
    S.prodPrimes_squarefree.squarefree_of_dvd (ChenEffective.smallSievePrimeProduct_dvd S 4000000)
  have hpr : Q.primeFactors = S.prodPrimes.primeFactors.filter
      (fun p : ℕ => (p:ℝ) < 4000000) := by
    apply Nat.primeFactors_prod
    intro p hp
    exact Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have hsize : ∀ p ∈ Q.primeFactors, p ≤ 4000000 := by
    intro p hp
    rw [hpr] at hp
    have hh := (mem_filter.mp hp).2
    exact_mod_cast hh.le
  constructor
  · exact reciprocal_divisor_moment_four_million_sharp hQ hsize
  · apply density_divisor_moment_four_million_sharp hQ hsize
      AnalyticNumberTheory.Sieve.goldbachNu AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
    · intro p hp
      exact (AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime
        (Nat.prime_of_mem_primeFactors hp)).le
    · intro p hp
      apply goldbach_root_prime_tight (Nat.prime_of_mem_primeFactors hp)
      have hd := (Nat.dvd_of_mem_primeFactors hp).trans
        (ChenEffective.smallSievePrimeProduct_dvd S 4000000)
      exact (MathlibNt.SieveTheory.SwitchingPrinciple.prime_dvd_jurkatRichertSourceSiftingProduct
        (Nat.prime_of_mem_primeFactors hp)).mp hd |>.1


#print axioms source_small_prime_divisor_moments_sharp
#print axioms density_divisor_moment_four_million_sharp

#print axioms prime_root_moment
end ChenEffective.GRH125
end
