import GRH125Moments

/-! Refined elementary moments. Mixed powers of two and three supply
logarithm bounds. Every rounded rational recurrence step is kernel checked. -/
noncomputable section
namespace ChenEffective.GRH122
open Real Finset
open ChenEffective.GRH125 (rootPrefix thetaPrefix theta_prefix_nonneg root_prefix_small root_prefix_step)
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem mixed_log_lower (k j a : ℕ) (hp : 2^k*3^j≤ a) :
    ((1386*k+2195*j:ℕ):ℝ)/2000≤ log (a:ℝ) := by
  have ha : (0:ℝ)<a := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0<(2:ℕ)^k*3^j) hp)
  have h3 : (439/400:ℝ)≤ log 3 := by
    have h := sum_range_le_log_div (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1) 4
    norm_num [Finset.sum_range_succ] at h
    linarith only [h]
  have h2 : (693/1000:ℝ)≤ log 2 := by linarith only [log_two_gt_d9]
  have h := log_le_log (by positivity : (0:ℝ)<(2:ℝ)^k*3^j) (show (2:ℝ)^k*3^j≤ a by exact_mod_cast hp)
  rw [log_mul (by positivity) (by positivity),log_pow,log_pow] at h
  push_cast
  nlinarith only [h,mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α:=ℝ) k),
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (α:=ℝ) j)]

theorem prime_root_moment (F : Finset ℕ) (hF : ∀ p∈F, p.Prime ∧ p≤4000000) :
    (∑ p∈F,1/sqrt (p:ℝ))≤465 := by
  classical
  have hprime : ∀ p∈F,p.Prime := fun p hp => (hF p hp).1
  have hsmall := root_prefix_small F hprime
  have hnonneg := theta_prefix_nonneg F hprime 100
  have h0 : rootPrefix F 100≤20+(8/365:ℝ)*thetaPrefix F 100 := by
    nlinarith only [hsmall,hnonneg]
  have h1 : rootPrefix F 121≤(204213/10000:ℝ)+(2000/102927:ℝ)*thetaPrefix F 121 := by
    apply root_prefix_step F hprime 100 121 (9125/2000) (20:ℝ) (204213/10000:ℝ) (2000/102927:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 1 100 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h0 using 1 <;> norm_num
    · norm_num
  have h2 : rootPrefix F 144≤(52391/2500:ℝ)+(250/14901:ℝ)*thetaPrefix F 144 := by
    apply root_prefix_step F hprime 121 144 (9357/2000) (204213/10000:ℝ) (52391/2500:ℝ) (250/14901:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 3 121 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h1 using 1 <;> norm_num
    · norm_num
  have h3 : rootPrefix F 169≤(106727/5000:ℝ)+(1000/66079:ℝ)*thetaPrefix F 169 := by
    apply root_prefix_step F hprime 144 169 (9934/2000) (52391/2500:ℝ) (106727/5000:ℝ) (1000/66079:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 2 144 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h2 using 1 <;> norm_num
    · norm_num
  have h4 : rootPrefix F 196≤(108843/5000:ℝ)+(1000/73577:ℝ)*thetaPrefix F 196 := by
    apply root_prefix_step F hprime 169 196 (10166/2000) (106727/5000:ℝ) (108843/5000:ℝ) (1000/73577:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 1 4 169 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h3 using 1 <;> norm_num
    · norm_num
  have h5 : rootPrefix F 225≤(55351/2500:ℝ)+(400/32229:ℝ)*thetaPrefix F 225 := by
    apply root_prefix_step F hprime 196 225 (10511/2000) (108843/5000:ℝ) (55351/2500:ℝ) (400/32229:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 1 196 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h4 using 1 <;> norm_num
    · norm_num
  have h6 : rootPrefix F 256≤(112741/5000:ℝ)+(125/11088:ℝ)*thetaPrefix F 256 := by
    apply root_prefix_step F hprime 225 256 (10743/2000) (55351/2500:ℝ) (112741/5000:ℝ) (125/11088:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 3 3 225 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h5 using 1 <;> norm_num
    · norm_num
  have h7 : rootPrefix F 289≤(45809/2000:ℝ)+(50/4811:ℝ)*thetaPrefix F 289 := by
    apply root_prefix_step F hprime 256 289 (11088/2000) (112741/5000:ℝ) (45809/2000:ℝ) (50/4811:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 0 256 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h6 using 1 <;> norm_num
    · norm_num
  have h8 : rootPrefix F 324≤(232559/10000:ℝ)+(125/12996:ℝ)*thetaPrefix F 324 := by
    apply root_prefix_step F hprime 289 324 (11320/2000) (45809/2000:ℝ) (232559/10000:ℝ) (125/12996:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 2 289 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h7 using 1 <;> norm_num
    · norm_num
  have h9 : rootPrefix F 361≤(117559/5000:ℝ)+(125/13718:ℝ)*thetaPrefix F 361 := by
    apply root_prefix_step F hprime 324 361 (11552/2000) (232559/10000:ℝ) (117559/5000:ℝ) (125/13718:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 4 324 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h8 using 1 <;> norm_num
    · norm_num
  have h10 : rootPrefix F 400≤(59769/2500:ℝ)+(100/11897:ℝ)*thetaPrefix F 400 := by
    apply root_prefix_step F hprime 361 400 (11552/2000) (117559/5000:ℝ) (59769/2500:ℝ) (100/11897:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 4 361 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h9 using 1 <;> norm_num
    · norm_num
  have h11 : rootPrefix F 441≤(242493/10000:ℝ)+(2000/254709:ℝ)*thetaPrefix F 441 := by
    apply root_prefix_step F hprime 400 441 (11897/2000) (59769/2500:ℝ) (242493/10000:ℝ) (2000/254709:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 1 400 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h10 using 1 <;> norm_num
    · norm_num
  have h12 : rootPrefix F 484≤(15307/625:ℝ)+(1000/133419:ℝ)*thetaPrefix F 484 := by
    apply root_prefix_step F hprime 441 484 (12129/2000) (242493/10000:ℝ) (15307/625:ℝ) (1000/133419:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 3 441 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h11 using 1 <;> norm_num
    · norm_num
  have h13 : rootPrefix F 529≤(124397/5000:ℝ)+(1000/143451:ℝ)*thetaPrefix F 529 := by
    apply root_prefix_step F hprime 484 529 (12129/2000) (15307/625:ℝ) (124397/5000:ℝ) (1000/143451:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 3 484 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h12 using 1 <;> norm_num
    · norm_num
  have h14 : rootPrefix F 576≤(6303/250:ℝ)+(125/19059:ℝ)*thetaPrefix F 576 := by
    apply root_prefix_step F hprime 529 576 (12474/2000) (124397/5000:ℝ) (6303/250:ℝ) (125/19059:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 0 529 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h13 using 1 <;> norm_num
    · norm_num
  have h15 : rootPrefix F 625≤(15901/625:ℝ)+(40/6353:ℝ)*thetaPrefix F 625 := by
    apply root_prefix_step F hprime 576 625 (12706/2000) (6303/250:ℝ) (15901/625:ℝ) (40/6353:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 2 576 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h14 using 1 <;> norm_num
    · norm_num
  have h16 : rootPrefix F 676≤(32217/1250:ℝ)+(500/84097:ℝ)*thetaPrefix F 676 := by
    apply root_prefix_step F hprime 625 676 (12706/2000) (15901/625:ℝ) (32217/1250:ℝ) (500/84097:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 2 625 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h15 using 1 <;> norm_num
    · norm_num
  have h17 : rootPrefix F 729≤(261013/10000:ℝ)+(200/35559:ℝ)*thetaPrefix F 729 := by
    apply root_prefix_step F hprime 676 729 (12938/2000) (32217/1250:ℝ) (261013/10000:ℝ) (200/35559:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 3 4 676 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h16 using 1 <;> norm_num
    · norm_num
  have h18 : rootPrefix F 784≤(10549/400:ℝ)+(500/92981:ℝ)*thetaPrefix F 784 := by
    apply root_prefix_step F hprime 729 784 (13170/2000) (261013/10000:ℝ) (10549/400:ℝ) (500/92981:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 0 6 729 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h17 using 1 <;> norm_num
    · norm_num
  have h19 : rootPrefix F 841≤(265909/10000:ℝ)+(2000/385207:ℝ)*thetaPrefix F 841 := by
    apply root_prefix_step F hprime 784 841 (13283/2000) (10549/400:ℝ) (265909/10000:ℝ) (2000/385207:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 1 784 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h18 using 1 <;> norm_num
    · norm_num
  have h20 : rootPrefix F 900≤(33647/1250:ℝ)+(40/8109:ℝ)*thetaPrefix F 900 := by
    apply root_prefix_step F hprime 841 900 (13283/2000) (265909/10000:ℝ) (33647/1250:ℝ) (40/8109:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 1 841 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h19 using 1 <;> norm_num
    · norm_num
  have h21 : rootPrefix F 961≤(271317/10000:ℝ)+(400/83793:ℝ)*thetaPrefix F 961 := by
    apply root_prefix_step F hprime 900 961 (13515/2000) (33647/1250:ℝ) (271317/10000:ℝ) (400/83793:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 3 900 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h20 using 1 <;> norm_num
    · norm_num
  have h22 : rootPrefix F 1024≤(137553/5000:ℝ)+(25/5544:ℝ)*thetaPrefix F 1024 := by
    apply root_prefix_step F hprime 961 1024 (13515/2000) (271317/10000:ℝ) (137553/5000:ℝ) (25/5544:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 3 961 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h21 using 1 <;> norm_num
    · norm_num
  have h23 : rootPrefix F 1089≤(27719/1000:ℝ)+(100/22869:ℝ)*thetaPrefix F 1089 := by
    apply root_prefix_step F hprime 1024 1089 (13860/2000) (137553/5000:ℝ) (27719/1000:ℝ) (100/22869:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 0 1024 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h22 using 1 <;> norm_num
    · norm_num
  have h24 : rootPrefix F 1156≤(280403/10000:ℝ)+(250/59891:ℝ)*thetaPrefix F 1156 := by
    apply root_prefix_step F hprime 1089 1156 (13860/2000) (27719/1000:ℝ) (280403/10000:ℝ) (250/59891:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 0 1089 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h23 using 1 <;> norm_num
    · norm_num
  have h25 : rootPrefix F 1296≤(28577/1000:ℝ)+(125/32229:ℝ)*thetaPrefix F 1296 := by
    apply root_prefix_step F hprime 1156 1296 (14092/2000) (280403/10000:ℝ) (28577/1000:ℝ) (125/32229:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 2 1156 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h24 using 1 <;> norm_num
    · norm_num
  have h26 : rootPrefix F 1444≤(289897/10000:ℝ)+(250/68039:ℝ)*thetaPrefix F 1444 := by
    apply root_prefix_step F hprime 1296 1444 (14324/2000) (28577/1000:ℝ) (289897/10000:ℝ) (250/68039:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 4 1296 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h25 using 1 <;> norm_num
    · norm_num
  have h27 : rootPrefix F 1600≤(73963/2500:ℝ)+(50/14669:ℝ)*thetaPrefix F 1600 := by
    apply root_prefix_step F hprime 1444 1600 (14324/2000) (289897/10000:ℝ) (73963/2500:ℝ) (50/14669:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 4 1444 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h26 using 1 <;> norm_num
    · norm_num
  have h28 : rootPrefix F 1764≤(301109/10000:ℝ)+(1000/312921:ℝ)*thetaPrefix F 1764 := by
    apply root_prefix_step F hprime 1600 1764 (14669/2000) (73963/2500:ℝ) (301109/10000:ℝ) (1000/312921:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 1 1600 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h27 using 1 <;> norm_num
    · norm_num
  have h29 : rootPrefix F 1936≤(305047/10000:ℝ)+(500/163911:ℝ)*thetaPrefix F 1936 := by
    apply root_prefix_step F hprime 1764 1936 (14901/2000) (301109/10000:ℝ) (305047/10000:ℝ) (500/163911:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 3 1764 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h28 using 1 <;> norm_num
    · norm_num
  have h30 : rootPrefix F 2116≤(77733/2500:ℝ)+(500/175329:ℝ)*thetaPrefix F 2116 := by
    apply root_prefix_step F hprime 1936 2116 (14901/2000) (305047/10000:ℝ) (77733/2500:ℝ) (500/175329:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 3 1936 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h29 using 1 <;> norm_num
    · norm_num
  have h31 : rootPrefix F 2304≤(316087/10000:ℝ)+(125/46434:ℝ)*thetaPrefix F 2304 := by
    apply root_prefix_step F hprime 2116 2304 (15246/2000) (77733/2500:ℝ) (316087/10000:ℝ) (125/46434:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 11 0 2116 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h30 using 1 <;> norm_num
    · norm_num
  have h32 : rootPrefix F 2500≤(19991/625:ℝ)+(20/7739:ℝ)*thetaPrefix F 2500 := by
    apply root_prefix_step F hprime 2304 2500 (15478/2000) (316087/10000:ℝ) (19991/625:ℝ) (20/7739:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 2 2304 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h31 using 1 <;> norm_num
    · norm_num
  have h33 : rootPrefix F 2704≤(20313/625:ℝ)+(50/20423:ℝ)*thetaPrefix F 2704 := by
    apply root_prefix_step F hprime 2500 2704 (15478/2000) (19991/625:ℝ) (20313/625:ℝ) (50/20423:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 2 2500 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h32 using 1 <;> norm_num
    · norm_num
  have h34 : rootPrefix F 2916≤(330111/10000:ℝ)+(500/215217:ℝ)*thetaPrefix F 2916 := by
    apply root_prefix_step F hprime 2704 2916 (15710/2000) (20313/625:ℝ) (330111/10000:ℝ) (500/215217:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 4 2704 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h33 using 1 <;> norm_num
    · norm_num
  have h35 : rootPrefix F 3136≤(334447/10000:ℝ)+(50/22477:ℝ)*thetaPrefix F 3136 := by
    apply root_prefix_step F hprime 2916 3136 (15942/2000) (330111/10000:ℝ) (334447/10000:ℝ) (50/22477:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 6 2916 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h34 using 1 <;> norm_num
    · norm_num
  have h36 : rootPrefix F 3364≤(16903/500:ℝ)+(200/93119:ℝ)*thetaPrefix F 3364 := by
    apply root_prefix_step F hprime 3136 3364 (16055/2000) (334447/10000:ℝ) (16903/500:ℝ) (200/93119:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 1 3136 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h35 using 1 <;> norm_num
    · norm_num
  have h37 : rootPrefix F 3600≤(343159/10000:ℝ)+(100/48861:ℝ)*thetaPrefix F 3600 := by
    apply root_prefix_step F hprime 3364 3600 (16055/2000) (16903/500:ℝ) (343159/10000:ℝ) (100/48861:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 1 3364 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h36 using 1 <;> norm_num
    · norm_num
  have h38 : rootPrefix F 3844≤(43339/1250:ℝ)+(1000/504897:ℝ)*thetaPrefix F 3844 := by
    apply root_prefix_step F hprime 3600 3844 (16287/2000) (343159/10000:ℝ) (43339/1250:ℝ) (1000/504897:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 3 3600 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h37 using 1 <;> norm_num
    · norm_num
  have h39 : rootPrefix F 4096≤(22034/625:ℝ)+(125/66528:ℝ)*thetaPrefix F 4096 := by
    apply root_prefix_step F hprime 3844 4096 (16287/2000) (43339/1250:ℝ) (22034/625:ℝ) (125/66528:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 3 3844 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h38 using 1 <;> norm_num
    · norm_num
  have h40 : rootPrefix F 4356≤(356017/10000:ℝ)+(125/68607:ℝ)*thetaPrefix F 4356 := by
    apply root_prefix_step F hprime 4096 4356 (16632/2000) (22034/625:ℝ) (356017/10000:ℝ) (125/68607:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 12 0 4096 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h39 using 1 <;> norm_num
    · norm_num
  have h41 : rootPrefix F 4624≤(361061/10000:ℝ)+(125/71672:ℝ)*thetaPrefix F 4624 := by
    apply root_prefix_step F hprime 4356 4624 (16632/2000) (356017/10000:ℝ) (361061/10000:ℝ) (125/71672:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 12 0 4356 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h40 using 1 <;> norm_num
    · norm_num
  have h42 : rootPrefix F 5041≤(183131/5000:ℝ)+(125/74834:ℝ)*thetaPrefix F 5041 := by
    apply root_prefix_step F hprime 4624 5041 (16864/2000) (361061/10000:ℝ) (183131/5000:ℝ) (125/74834:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 2 4624 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h41 using 1 <;> norm_num
    · norm_num
  have h43 : rootPrefix F 5476≤(373121/10000:ℝ)+(125/79069:ℝ)*thetaPrefix F 5476 := by
    apply root_prefix_step F hprime 5041 5476 (16864/2000) (183131/5000:ℝ) (373121/10000:ℝ) (125/79069:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 2 5041 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h42 using 1 <;> norm_num
    · norm_num
  have h44 : rootPrefix F 5929≤(379923/10000:ℝ)+(125/83391:ℝ)*thetaPrefix F 5929 := by
    apply root_prefix_step F hprime 5476 5929 (17096/2000) (373121/10000:ℝ) (379923/10000:ℝ) (125/83391:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 4 5476 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h43 using 1 <;> norm_num
    · norm_num
  have h45 : rootPrefix F 6400≤(192899/5000:ℝ)+(25/17441:ℝ)*thetaPrefix F 6400 := by
    apply root_prefix_step F hprime 5929 6400 (17328/2000) (379923/10000:ℝ) (192899/5000:ℝ) (25/17441:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 3 6 5929 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h44 using 1 <;> norm_num
    · norm_num
  have h46 : rootPrefix F 6889≤(195849/5000:ℝ)+(50/36437:ℝ)*thetaPrefix F 6889 := by
    apply root_prefix_step F hprime 6400 6889 (17441/2000) (192899/5000:ℝ) (195849/5000:ℝ) (50/36437:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 11 1 6400 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h45 using 1 <;> norm_num
    · norm_num
  have h47 : rootPrefix F 7396≤(99383/2500:ℝ)+(1000/759939:ℝ)*thetaPrefix F 7396 := by
    apply root_prefix_step F hprime 6889 7396 (17560/2000) (195849/5000:ℝ) (99383/2500:ℝ) (1000/759939:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 0 8 6889 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h46 using 1 <;> norm_num
    · norm_num
  have h48 : rootPrefix F 7921≤(202139/5000:ℝ)+(400/318709:ℝ)*thetaPrefix F 7921 := by
    apply root_prefix_step F hprime 7396 7921 (17673/2000) (99383/2500:ℝ) (202139/5000:ℝ) (400/318709:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 3 7396 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h47 using 1 <;> norm_num
    · norm_num
  have h49 : rootPrefix F 8464≤(41003/1000:ℝ)+(250/207207:ℝ)*thetaPrefix F 8464 := by
    apply root_prefix_step F hprime 7921 8464 (17905/2000) (202139/5000:ℝ) (41003/1000:ℝ) (250/207207:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 5 7921 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h48 using 1 <;> norm_num
    · norm_num
  have h50 : rootPrefix F 9025≤(415813/10000:ℝ)+(400/344603:ℝ)*thetaPrefix F 9025 := by
    apply root_prefix_step F hprime 8464 9025 (18018/2000) (41003/1000:ℝ) (415813/10000:ℝ) (400/344603:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 13 0 8464 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h49 using 1 <;> norm_num
    · norm_num
  have h51 : rootPrefix F 9604≤(52691/1250:ℝ)+(4/3577:ℝ)*thetaPrefix F 9604 := by
    apply root_prefix_step F hprime 9025 9604 (18137/2000) (415813/10000:ℝ) (52691/1250:ℝ) (4/3577:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 7 9025 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h50 using 1 <;> norm_num
    · norm_num
  have h52 : rootPrefix F 10201≤(26642/625:ℝ)+(8/7373:ℝ)*thetaPrefix F 10201 := by
    apply root_prefix_step F hprime 9604 10201 (18250/2000) (52691/1250:ℝ) (26642/625:ℝ) (8/7373:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 2 9604 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h51 using 1 <;> norm_num
    · norm_num
  have h53 : rootPrefix F 11025≤(17387/400:ℝ)+(200/194061:ℝ)*thetaPrefix F 11025 := by
    apply root_prefix_step F hprime 10201 11025 (18250/2000) (26642/625:ℝ) (17387/400:ℝ) (200/194061:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 2 10201 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h52 using 1 <;> norm_num
    · norm_num
  have h54 : rootPrefix F 11881≤(443013/10000:ℝ)+(1000/1019913:ℝ)*thetaPrefix F 11881 := by
    apply root_prefix_step F hprime 11025 11881 (18482/2000) (17387/400:ℝ) (443013/10000:ℝ) (1000/1019913:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 4 11025 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h53 using 1 <;> norm_num
    · norm_num
  have h55 : rootPrefix F 12769≤(450233/10000:ℝ)+(2000/2127451:ℝ)*thetaPrefix F 12769 := by
    apply root_prefix_step F hprime 11881 12769 (18714/2000) (443013/10000:ℝ) (450233/10000:ℝ) (2000/2127451:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 6 11881 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h54 using 1 <;> norm_num
    · norm_num
  have h56 : rootPrefix F 13689≤(228743/5000:ℝ)+(1000/1108341:ℝ)*thetaPrefix F 13689 := by
    apply root_prefix_step F hprime 12769 13689 (18827/2000) (450233/10000:ℝ) (228743/5000:ℝ) (1000/1108341:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 12 1 12769 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h55 using 1 <;> norm_num
    · norm_num
  have h57 : rootPrefix F 14641≤(23233/500:ℝ)+(2000/2306139:ℝ)*thetaPrefix F 14641 := by
    apply root_prefix_step F hprime 13689 14641 (18946/2000) (228743/5000:ℝ) (23233/500:ℝ) (2000/2306139:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 1 8 13689 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h56 using 1 <;> norm_num
    · norm_num
  have h58 : rootPrefix F 15625≤(23647/500:ℝ)+(16/19291:ℝ)*thetaPrefix F 15625 := by
    apply root_prefix_step F hprime 14641 15625 (19059/2000) (23233/500:ℝ) (23647/500:ℝ) (16/19291:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 3 14641 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h57 using 1 <;> norm_num
    · norm_num
  have h59 : rootPrefix F 16641≤(240011/5000:ℝ)+(500/625779:ℝ)*thetaPrefix F 16641 := by
    apply root_prefix_step F hprime 15625 16641 (19291/2000) (23647/500:ℝ) (240011/5000:ℝ) (500/625779:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 5 15625 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h58 using 1 <;> norm_num
    · norm_num
  have h60 : rootPrefix F 17689≤(487143/10000:ℝ)+(2000/2596559:ℝ)*thetaPrefix F 17689 := by
    apply root_prefix_step F hprime 16641 17689 (19404/2000) (240011/5000:ℝ) (487143/10000:ℝ) (2000/2596559:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 14 0 16641 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h59 using 1 <;> norm_num
    · norm_num
  have h61 : rootPrefix F 18769≤(61773/1250:ℝ)+(500/672533:ℝ)*thetaPrefix F 18769 := by
    apply root_prefix_step F hprime 17689 18769 (19523/2000) (487143/10000:ℝ) (61773/1250:ℝ) (500/672533:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 3 7 17689 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h60 using 1 <;> norm_num
    · norm_num
  have h62 : rootPrefix F 20164≤(251397/5000:ℝ)+(200/280521:ℝ)*thetaPrefix F 20164 := by
    apply root_prefix_step F hprime 18769 20164 (19636/2000) (61773/1250:ℝ) (251397/5000:ℝ) (200/280521:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 11 2 18769 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h61 using 1 <;> norm_num
    · norm_num
  have h63 : rootPrefix F 21609≤(127829/2500:ℝ)+(500/730149:ℝ)*thetaPrefix F 21609 := by
    apply root_prefix_step F hprime 20164 21609 (19755/2000) (251397/5000:ℝ) (127829/2500:ℝ) (500/730149:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 0 9 20164 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h62 using 1 <;> norm_num
    · norm_num
  have h64 : rootPrefix F 23104≤(518603/10000:ℝ)+(125/188746:ℝ)*thetaPrefix F 23104 := by
    apply root_prefix_step F hprime 21609 23104 (19868/2000) (127829/2500:ℝ) (518603/10000:ℝ) (125/188746:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 4 21609 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h63 using 1 <;> norm_num
    · norm_num
  have h65 : rootPrefix F 24649≤(264829/5000:ℝ)+(2000/3173441:ℝ)*thetaPrefix F 24649 := by
    apply root_prefix_step F hprime 23104 24649 (19868/2000) (518603/10000:ℝ) (264829/5000:ℝ) (2000/3173441:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 4 23104 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h64 using 1 <;> norm_num
    · norm_num
  have h66 : rootPrefix F 26244≤(538119/10000:ℝ)+(250/411723:ℝ)*thetaPrefix F 26244 := by
    apply root_prefix_step F hprime 24649 26244 (20213/2000) (264829/5000:ℝ) (538119/10000:ℝ) (250/411723:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 13 1 24649 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h65 using 1 <;> norm_num
    · norm_num
  have h67 : rootPrefix F 27889≤(546489/10000:ℝ)+(400/682863:ℝ)*thetaPrefix F 27889 := by
    apply root_prefix_step F hprime 26244 27889 (20332/2000) (538119/10000:ℝ) (546489/10000:ℝ) (400/682863:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 8 26244 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h66 using 1 <;> norm_num
    · norm_num
  have h68 : rootPrefix F 29929≤(277501/5000:ℝ)+(400/707397:ℝ)*thetaPrefix F 29929 := by
    apply root_prefix_step F hprime 27889 29929 (20445/2000) (546489/10000:ℝ) (277501/5000:ℝ) (400/707397:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 3 27889 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h67 using 1 <;> norm_num
    · norm_num
  have h69 : rootPrefix F 32041≤(113251/2000:ℝ)+(2000/3701183:ℝ)*thetaPrefix F 32041 := by
    apply root_prefix_step F hprime 29929 32041 (20445/2000) (277501/5000:ℝ) (113251/2000:ℝ) (2000/3701183:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 3 29929 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h68 using 1 <;> norm_num
    · norm_num
  have h70 : rootPrefix F 34225≤(288007/5000:ℝ)+(40/76923:ℝ)*thetaPrefix F 34225 := by
    apply root_prefix_step F hprime 32041 34225 (20677/2000) (113251/2000:ℝ) (288007/5000:ℝ) (40/76923:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 5 32041 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h69 using 1 <;> norm_num
    · norm_num
  have h71 : rootPrefix F 36481≤(585821/10000:ℝ)+(2000/3993619:ℝ)*thetaPrefix F 36481 := by
    apply root_prefix_step F hprime 34225 36481 (20790/2000) (288007/5000:ℝ) (585821/10000:ℝ) (2000/3993619:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 15 0 34225 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h70 using 1 <;> norm_num
    · norm_num
  have h72 : rootPrefix F 38809≤(595527/10000:ℝ)+(1000/2070667:ℝ)*thetaPrefix F 38809 := by
    apply root_prefix_step F hprime 36481 38809 (20909/2000) (585821/10000:ℝ) (595527/10000:ℝ) (1000/2070667:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 7 36481 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h71 using 1 <;> norm_num
    · norm_num
  have h73 : rootPrefix F 41209≤(151321/2500:ℝ)+(2000/4291623:ℝ)*thetaPrefix F 41209 := by
    apply root_prefix_step F hprime 38809 41209 (21022/2000) (595527/10000:ℝ) (151321/2500:ℝ) (2000/4291623:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 12 2 38809 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h72 using 1 <;> norm_num
    · norm_num
  have h74 : rootPrefix F 44100≤(308177/5000:ℝ)+(100/223167:ℝ)*thetaPrefix F 44100 := by
    apply root_prefix_step F hprime 41209 44100 (21141/2000) (151321/2500:ℝ) (308177/5000:ℝ) (100/223167:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 1 9 41209 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h73 using 1 <;> norm_num
    · norm_num
  have h75 : rootPrefix F 47089≤(62897/1000:ℝ)+(1000/2331231:ℝ)*thetaPrefix F 47089 := by
    apply root_prefix_step F hprime 44100 47089 (21254/2000) (308177/5000:ℝ) (62897/1000:ℝ) (1000/2331231:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 4 44100 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h74 using 1 <;> norm_num
    · norm_num
  have h76 : rootPrefix F 50176≤(319957/5000:ℝ)+(125/302386:ℝ)*thetaPrefix F 50176 := by
    apply root_prefix_step F hprime 47089 50176 (21486/2000) (62897/1000:ℝ) (319957/5000:ℝ) (125/302386:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 6 47089 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h75 using 1 <;> norm_num
    · norm_num
  have h77 : rootPrefix F 53361≤(650913/10000:ℝ)+(1000/2508429:ℝ)*thetaPrefix F 53361 := by
    apply root_prefix_step F hprime 50176 53361 (21599/2000) (319957/5000:ℝ) (650913/10000:ℝ) (1000/2508429:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 14 1 50176 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h76 using 1 <;> norm_num
    · norm_num
  have h78 : rootPrefix F 56644≤(3309/50:ℝ)+(1000/2597889:ℝ)*thetaPrefix F 56644 := by
    apply root_prefix_step F hprime 53361 56644 (21718/2000) (650913/10000:ℝ) (3309/50:ℝ) (1000/2597889:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 3 8 53361 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h77 using 1 <;> norm_num
    · norm_num
  have h79 : rootPrefix F 60516≤(674117/10000:ℝ)+(20/53997:ℝ)*thetaPrefix F 60516 := by
    apply root_prefix_step F hprime 56644 60516 (21831/2000) (3309/50:ℝ) (674117/10000:ℝ) (20/53997:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 11 3 56644 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h78 using 1 <;> norm_num
    · norm_num
  have h80 : rootPrefix F 64516≤(343157/5000:ℝ)+(1000/2802001:ℝ)*thetaPrefix F 64516 := by
    apply root_prefix_step F hprime 60516 64516 (21950/2000) (674117/10000:ℝ) (343157/5000:ℝ) (1000/2802001:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 0 10 60516 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h79 using 1 <;> norm_num
    · norm_num
  have h81 : rootPrefix F 68644≤(698481/10000:ℝ)+(125/363132:ℝ)*thetaPrefix F 68644 := by
    apply root_prefix_step F hprime 64516 68644 (22063/2000) (343157/5000:ℝ) (698481/10000:ℝ) (125/363132:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 5 64516 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h80 using 1 <;> norm_num
    · norm_num
  have h82 : rootPrefix F 72900≤(710711/10000:ℝ)+(40/120393:ℝ)*thetaPrefix F 72900 := by
    apply root_prefix_step F hprime 68644 72900 (22176/2000) (698481/10000:ℝ) (710711/10000:ℝ) (40/120393:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 16 0 68644 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h81 using 1 <;> norm_num
    · norm_num
  have h83 : rootPrefix F 77841≤(362079/5000:ℝ)+(250/781479:ℝ)*thetaPrefix F 77841 := by
    apply root_prefix_step F hprime 72900 77841 (22295/2000) (710711/10000:ℝ) (362079/5000:ℝ) (250/781479:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 7 72900 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h82 using 1 <;> norm_num
    · norm_num
  have h84 : rootPrefix F 82944≤(147891/2000:ℝ)+(25/81504:ℝ)*thetaPrefix F 82944 := by
    apply root_prefix_step F hprime 77841 82944 (22408/2000) (362079/5000:ℝ) (147891/2000:ℝ) (25/81504:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 13 2 77841 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h83 using 1 <;> norm_num
    · norm_num
  have h85 : rootPrefix F 88209≤(375467/5000:ℝ)+(25/84051:ℝ)*thetaPrefix F 88209 := by
    apply root_prefix_step F hprime 82944 88209 (22640/2000) (147891/2000:ℝ) (375467/5000:ℝ) (25/84051:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 4 82944 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h84 using 1 <;> norm_num
    · norm_num
  have h86 : rootPrefix F 93636≤(766241/10000:ℝ)+(125/437427:ℝ)*thetaPrefix F 93636 := by
    apply root_prefix_step F hprime 88209 93636 (22640/2000) (375467/5000:ℝ) (766241/10000:ℝ) (125/437427:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 4 88209 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h85 using 1 <;> norm_num
    · norm_num
  have h87 : rootPrefix F 99856≤(156157/2000:ℝ)+(100/363163:ℝ)*thetaPrefix F 99856 := by
    apply root_prefix_step F hprime 93636 99856 (22872/2000) (766241/10000:ℝ) (156157/2000:ℝ) (100/363163:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 6 93636 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h86 using 1 <;> norm_num
    · norm_num
  have h88 : rootPrefix F 106276≤(397699/5000:ℝ)+(125/470744:ℝ)*thetaPrefix F 106276 := by
    apply root_prefix_step F hprime 99856 106276 (22985/2000) (156157/2000:ℝ) (397699/5000:ℝ) (125/470744:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 15 1 99856 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h87 using 1 <;> norm_num
    · norm_num
  have h89 : rootPrefix F 112896≤(809871/10000:ℝ)+(125/487557:ℝ)*thetaPrefix F 112896 := by
    apply root_prefix_step F hprime 106276 112896 (23104/2000) (397699/5000:ℝ) (809871/10000:ℝ) (125/487557:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 8 106276 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h88 using 1 <;> norm_num
    · norm_num
  have h90 : rootPrefix F 120409≤(412853/5000:ℝ)+(250/1012199:ℝ)*thetaPrefix F 120409 := by
    apply root_prefix_step F hprime 112896 120409 (23217/2000) (809871/10000:ℝ) (412853/5000:ℝ) (250/1012199:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 12 3 112896 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h89 using 1 <;> norm_num
    · norm_num
  have h91 : rootPrefix F 128164≤(841393/10000:ℝ)+(1000/4197371:ℝ)*thetaPrefix F 128164 := by
    apply root_prefix_step F hprime 120409 128164 (23336/2000) (412853/5000:ℝ) (841393/10000:ℝ) (1000/4197371:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 1 10 120409 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h90 using 1 <;> norm_num
    · norm_num
  have h92 : rootPrefix F 136161≤(171409/2000:ℝ)+(1000/4347189:ℝ)*thetaPrefix F 136161 := by
    apply root_prefix_step F hprime 128164 136161 (23449/2000) (841393/10000:ℝ) (171409/2000:ℝ) (1000/4347189:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 5 128164 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h91 using 1 <;> norm_num
    · norm_num
  have h93 : rootPrefix F 145161≤(174809/2000:ℝ)+(2000/9022461:ℝ)*thetaPrefix F 145161 := by
    apply root_prefix_step F hprime 136161 145161 (23562/2000) (171409/2000:ℝ) (174809/2000:ℝ) (2000/9022461:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 17 0 136161 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h92 using 1 <;> norm_num
    · norm_num
  have h94 : rootPrefix F 154449≤(111361/1250:ℝ)+(1000/4675521:ℝ)*thetaPrefix F 154449 := by
    apply root_prefix_step F hprime 145161 154449 (23681/2000) (174809/2000:ℝ) (111361/1250:ℝ) (1000/4675521:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 7 145161 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h93 using 1 <;> norm_num
    · norm_num
  have h95 : rootPrefix F 164025≤(907813/10000:ℝ)+(400/1936953:ℝ)*thetaPrefix F 164025 := by
    apply root_prefix_step F hprime 154449 164025 (23794/2000) (111361/1250:ℝ) (907813/10000:ℝ) (400/1936953:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 14 2 154449 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h94 using 1 <;> norm_num
    · norm_num
  have h96 : rootPrefix F 174724≤(462913/5000:ℝ)+(500/2510717:ℝ)*thetaPrefix F 174724 := by
    apply root_prefix_step F hprime 164025 174724 (23913/2000) (907813/10000:ℝ) (462913/5000:ℝ) (500/2510717:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 3 9 164025 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h95 using 1 <;> norm_num
    · norm_num
  have h97 : rootPrefix F 185761≤(943923/10000:ℝ)+(400/2081299:ℝ)*thetaPrefix F 185761 := by
    apply root_prefix_step F hprime 174724 185761 (24026/2000) (462913/5000:ℝ) (943923/10000:ℝ) (400/2081299:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 11 4 174724 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h96 using 1 <;> norm_num
    · norm_num
  have h98 : rootPrefix F 197136≤(964229/10000:ℝ)+(500/2705181:ℝ)*thetaPrefix F 197136 := by
    apply root_prefix_step F hprime 185761 197136 (24145/2000) (943923/10000:ℝ) (964229/10000:ℝ) (500/2705181:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 0 11 185761 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h97 using 1 <;> norm_num
    · norm_num
  have h99 : rootPrefix F 209764≤(980821/10000:ℝ)+(1000/5580959:ℝ)*thetaPrefix F 209764 := by
    apply root_prefix_step F hprime 197136 209764 (24371/2000) (964229/10000:ℝ) (980821/10000:ℝ) (1000/5580959:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 16 1 197136 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h98 using 1 <;> norm_num
    · norm_num
  have h100 : rootPrefix F 222784≤(1002511/10000:ℝ)+(250/1451577:ℝ)*thetaPrefix F 222784 := by
    apply root_prefix_step F hprime 209764 222784 (24371/2000) (980821/10000:ℝ) (1002511/10000:ℝ) (250/1451577:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 16 1 209764 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h99 using 1 <;> norm_num
    · norm_num
  have h101 : rootPrefix F 237169≤(1022793/10000:ℝ)+(1000/6019807:ℝ)*thetaPrefix F 237169 := by
    apply root_prefix_step F hprime 222784 237169 (24603/2000) (1002511/10000:ℝ) (1022793/10000:ℝ) (1000/6019807:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 13 3 222784 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h100 using 1 <;> norm_num
    · norm_num
  have h102 : rootPrefix F 252004≤(1042893/10000:ℝ)+(200/1246717:ℝ)*thetaPrefix F 252004 := by
    apply root_prefix_step F hprime 237169 252004 (24722/2000) (1022793/10000:ℝ) (1042893/10000:ℝ) (200/1246717:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 10 237169 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h101 using 1 <;> norm_num
    · norm_num
  have h103 : rootPrefix F 268324≤(1064153/10000:ℝ)+(250/1615383:ℝ)*thetaPrefix F 268324 := by
    apply root_prefix_step F hprime 252004 268324 (24835/2000) (1042893/10000:ℝ) (1064153/10000:ℝ) (250/1615383:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 5 252004 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h102 using 1 <;> norm_num
    · norm_num
  have h104 : rootPrefix F 285156≤(1085511/10000:ℝ)+(1000/6692889:ℝ)*thetaPrefix F 285156 := by
    apply root_prefix_step F hprime 268324 285156 (24948/2000) (1064153/10000:ℝ) (1085511/10000:ℝ) (1000/6692889:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 18 0 268324 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h103 using 1 <;> norm_num
    · norm_num
  have h105 : rootPrefix F 303601≤(1107867/10000:ℝ)+(100/693709:ℝ)*thetaPrefix F 303601 := by
    apply root_prefix_step F hprime 285156 303601 (25067/2000) (1085511/10000:ℝ) (1107867/10000:ℝ) (100/693709:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 7 285156 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h104 using 1 <;> norm_num
    · norm_num
  have h106 : rootPrefix F 322624≤(565163/5000:ℝ)+(250/1796229:ℝ)*thetaPrefix F 322624 := by
    apply root_prefix_step F hprime 303601 322624 (25180/2000) (1107867/10000:ℝ) (565163/5000:ℝ) (250/1796229:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 15 2 303601 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h105 using 1 <;> norm_num
    · norm_num
  have h107 : rootPrefix F 343396≤(288441/2500:ℝ)+(250/1861429:ℝ)*thetaPrefix F 343396 := by
    apply root_prefix_step F hprime 322624 343396 (25299/2000) (565163/5000:ℝ) (288441/2500:ℝ) (250/1861429:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 9 322624 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h106 using 1 <;> norm_num
    · norm_num
  have h108 : rootPrefix F 364816≤(1177309/10000:ℝ)+(500/3855181:ℝ)*thetaPrefix F 364816 := by
    apply root_prefix_step F hprime 343396 364816 (25412/2000) (288441/2500:ℝ) (1177309/10000:ℝ) (500/3855181:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 12 4 343396 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h107 using 1 <;> norm_num
    · norm_num
  have h109 : rootPrefix F 388129≤(1201813/10000:ℝ)+(500/3994053:ℝ)*thetaPrefix F 388129 := by
    apply root_prefix_step F hprime 364816 388129 (25531/2000) (1177309/10000:ℝ) (1201813/10000:ℝ) (500/3994053:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 1 11 364816 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h108 using 1 <;> norm_num
    · norm_num
  have h110 : rootPrefix F 412164≤(1226267/10000:ℝ)+(1000/8267997:ℝ)*thetaPrefix F 412164 := by
    apply root_prefix_step F hprime 388129 412164 (25644/2000) (1201813/10000:ℝ) (1226267/10000:ℝ) (1000/8267997:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 6 388129 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h109 using 1 <;> norm_num
    · norm_num
  have h111 : rootPrefix F 438244≤(312999/2500:ℝ)+(250/2141239:ℝ)*thetaPrefix F 438244 := by
    apply root_prefix_step F hprime 412164 438244 (25757/2000) (1226267/10000:ℝ) (312999/2500:ℝ) (250/2141239:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 17 1 412164 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h110 using 1 <;> norm_num
    · norm_num
  have h112 : rootPrefix F 465124≤(1277501/10000:ℝ)+(1000/8862249:ℝ)*thetaPrefix F 465124 := by
    apply root_prefix_step F hprime 438244 465124 (25876/2000) (312999/2500:ℝ) (1277501/10000:ℝ) (1000/8862249:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 8 438244 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h111 using 1 <;> norm_num
    · norm_num
  have h113 : rootPrefix F 494209≤(52171/400:ℝ)+(500/4588481:ℝ)*thetaPrefix F 494209 := by
    apply root_prefix_step F hprime 465124 494209 (25989/2000) (1277501/10000:ℝ) (52171/400:ℝ) (500/4588481:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 14 3 465124 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h112 using 1 <;> norm_num
    · norm_num
  have h114 : rootPrefix F 525625≤(1335281/10000:ℝ)+(40/381843:ℝ)*thetaPrefix F 525625 := by
    apply root_prefix_step F hprime 494209 525625 (26108/2000) (52171/400:ℝ) (1335281/10000:ℝ) (40/381843:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 3 10 494209 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h113 using 1 <;> norm_num
    · norm_num
  have h115 : rootPrefix F 558009≤(339891/2500:ℝ)+(100/983799:ℝ)*thetaPrefix F 558009 := by
    apply root_prefix_step F hprime 525625 558009 (26334/2000) (1335281/10000:ℝ) (339891/2500:ℝ) (100/983799:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 19 0 525625 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h114 using 1 <;> norm_num
    · norm_num
  have h116 : rootPrefix F 592900≤(139173/1000:ℝ)+(100/1022791:ℝ)*thetaPrefix F 592900 := by
    apply root_prefix_step F hprime 558009 592900 (26340/2000) (339891/2500:ℝ) (139173/1000:ℝ) (100/1022791:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 0 12 558009 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h115 using 1 <;> norm_num
    · norm_num
  have h117 : rootPrefix F 630436≤(710773/5000:ℝ)+(200/2118789:ℝ)*thetaPrefix F 630436 := by
    apply root_prefix_step F hprime 592900 630436 (26566/2000) (139173/1000:ℝ) (710773/5000:ℝ) (200/2118789:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 16 2 592900 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h116 using 1 <;> norm_num
    · norm_num
  have h118 : rootPrefix F 669124≤(145111/1000:ℝ)+(500/5480191:ℝ)*thetaPrefix F 669124 := by
    apply root_prefix_step F hprime 630436 669124 (26685/2000) (710773/5000:ℝ) (145111/1000:ℝ) (500/5480191:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 9 630436 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h117 using 1 <;> norm_num
    · norm_num
  have h119 : rootPrefix F 710649≤(370481/2500:ℝ)+(2000/22691031:ℝ)*thetaPrefix F 710649 := by
    apply root_prefix_step F hprime 669124 710649 (26798/2000) (145111/1000:ℝ) (370481/2500:ℝ) (2000/22691031:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 13 4 669124 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h118 using 1 <;> norm_num
    · norm_num
  have h120 : rootPrefix F 755161≤(94599/625:ℝ)+(200/2348907:ℝ)*thetaPrefix F 755161 := by
    apply root_prefix_step F hprime 710649 755161 (26917/2000) (370481/2500:ℝ) (94599/625:ℝ) (200/2348907:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 11 710649 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h119 using 1 <;> norm_num
    · norm_num
  have h121 : rootPrefix F 802816≤(773143/5000:ℝ)+(125/1520008:ℝ)*thetaPrefix F 802816 := by
    apply root_prefix_step F hprime 755161 802816 (27030/2000) (94599/625:ℝ) (773143/5000:ℝ) (125/1520008:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 10 6 755161 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h120 using 1 <;> norm_num
    · norm_num
  have h122 : rootPrefix F 851929≤(789567/5000:ℝ)+(1000/12581413:ℝ)*thetaPrefix F 851929 := by
    apply root_prefix_step F hprime 802816 851929 (27143/2000) (773143/5000:ℝ) (789567/5000:ℝ) (1000/12581413:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 18 1 802816 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h121 using 1 <;> norm_num
    · norm_num
  have h123 : rootPrefix F 904401≤(1612797/10000:ℝ)+(16/208269:ℝ)*thetaPrefix F 904401 := by
    apply root_prefix_step F hprime 851929 904401 (27262/2000) (789567/5000:ℝ) (1612797/10000:ℝ) (16/208269:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 7 8 851929 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h122 using 1 <;> norm_num
    · norm_num
  have h124 : rootPrefix F 960400≤(1647703/10000:ℝ)+(50/673603:ℝ)*thetaPrefix F 960400 := by
    apply root_prefix_step F hprime 904401 960400 (27375/2000) (1612797/10000:ℝ) (1647703/10000:ℝ) (50/673603:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 15 3 904401 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h123 using 1 <;> norm_num
    · norm_num
  have h125 : rootPrefix F 1020100≤(1683401/10000:ℝ)+(200/2788307:ℝ)*thetaPrefix F 1020100 := by
    apply root_prefix_step F hprime 960400 1020100 (27494/2000) (1647703/10000:ℝ) (1683401/10000:ℝ) (200/2788307:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 4 10 960400 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h124 using 1 <;> norm_num
    · norm_num
  have h126 : rootPrefix F 1083681≤(1720339/10000:ℝ)+(1000/14431383:ℝ)*thetaPrefix F 1083681 := by
    apply root_prefix_step F hprime 1020100 1083681 (27607/2000) (1683401/10000:ℝ) (1720339/10000:ℝ) (1000/14431383:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 12 5 1020100 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h125 using 1 <;> norm_num
    · norm_num
  have h127 : rootPrefix F 1151329≤(109878/625:ℝ)+(2000/29871247:ℝ)*thetaPrefix F 1151329 := by
    apply root_prefix_step F hprime 1083681 1151329 (27726/2000) (1720339/10000:ℝ) (109878/625:ℝ) (2000/29871247:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 1 12 1083681 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h126 using 1 <;> norm_num
    · norm_num
  have h128 : rootPrefix F 1223236≤(1796757/10000:ℝ)+(125/1932182:ℝ)*thetaPrefix F 1223236 := by
    apply root_prefix_step F hprime 1151329 1223236 (27839/2000) (109878/625:ℝ) (1796757/10000:ℝ) (125/1932182:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 7 1151329 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h127 using 1 <;> norm_num
    · norm_num
  have h129 : rootPrefix F 1299600≤(114794/625:ℝ)+(100/1600047:ℝ)*thetaPrefix F 1299600 := by
    apply root_prefix_step F hprime 1223236 1299600 (27952/2000) (1796757/10000:ℝ) (114794/625:ℝ) (100/1600047:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 17 2 1223236 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h128 using 1 <;> norm_num
    · norm_num
  have h130 : rootPrefix F 1380625≤(1877387/10000:ℝ)+(10/165581:ℝ)*thetaPrefix F 1380625 := by
    apply root_prefix_step F hprime 1299600 1380625 (28071/2000) (114794/625:ℝ) (1877387/10000:ℝ) (10/165581:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 9 1299600 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h129 using 1 <;> norm_num
    · norm_num
  have h131 : rootPrefix F 1466521≤(1919307/10000:ℝ)+(2000/34274933:ℝ)*thetaPrefix F 1466521 := by
    apply root_prefix_step F hprime 1380625 1466521 (28184/2000) (1877387/10000:ℝ) (1919307/10000:ℝ) (2000/34274933:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 14 4 1380625 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h130 using 1 <;> norm_num
    · norm_num
  have h132 : rootPrefix F 1557504≤(1961939/10000:ℝ)+(125/2216448:ℝ)*thetaPrefix F 1557504 := by
    apply root_prefix_step F hprime 1466521 1557504 (28303/2000) (1919307/10000:ℝ) (1961939/10000:ℝ) (125/2216448:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 3 11 1466521 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h131 using 1 <;> norm_num
    · norm_num
  have h133 : rootPrefix F 1653796≤(125363/625:ℝ)+(200/3669601:ℝ)*thetaPrefix F 1653796 := by
    apply root_prefix_step F hprime 1557504 1653796 (28416/2000) (1961939/10000:ℝ) (125363/625:ℝ) (200/3669601:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 11 6 1557504 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h132 using 1 <;> norm_num
    · norm_num
  have h134 : rootPrefix F 1755625≤(1025183/5000:ℝ)+(10/189793:ℝ)*thetaPrefix F 1755625 := by
    apply root_prefix_step F hprime 1653796 1755625 (28535/2000) (125363/625:ℝ) (1025183/5000:ℝ) (10/189793:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 0 13 1653796 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h133 using 1 <;> norm_num
    · norm_num
  have h135 : rootPrefix F 1863225≤(523971/2500:ℝ)+(400/7851753:ℝ)*thetaPrefix F 1863225 := by
    apply root_prefix_step F hprime 1755625 1863225 (28648/2000) (1025183/5000:ℝ) (523971/2500:ℝ) (400/7851753:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 8 8 1755625 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h134 using 1 <;> norm_num
    · norm_num
  have h136 : rootPrefix F 1976836≤(2142639/10000:ℝ)+(25/507566:ℝ)*thetaPrefix F 1976836 := by
    apply root_prefix_step F hprime 1863225 1976836 (28761/2000) (523971/2500:ℝ) (2142639/10000:ℝ) (25/507566:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 16 3 1863225 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h135 using 1 <;> norm_num
    · norm_num
  have h137 : rootPrefix F 2099601≤(2196513/10000:ℝ)+(1000/21087297:ℝ)*thetaPrefix F 2099601 := by
    apply root_prefix_step F hprime 1976836 2099601 (28880/2000) (2142639/10000:ℝ) (2196513/10000:ℝ) (1000/21087297:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 5 10 1976836 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h136 using 1 <;> norm_num
    · norm_num
  have h138 : rootPrefix F 2229049≤(2240423/10000:ℝ)+(250/5433027:ℝ)*thetaPrefix F 2229049 := by
    apply root_prefix_step F hprime 2099601 2229049 (29106/2000) (2196513/10000:ℝ) (2240423/10000:ℝ) (250/5433027:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 21 0 2099601 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h137 using 1 <;> norm_num
    · norm_num
  have h139 : rootPrefix F 2365444≤(574101/2500:ℝ)+(500/11280461:ℝ)*thetaPrefix F 2365444 := by
    apply root_prefix_step F hprime 2229049 2365444 (29112/2000) (2240423/10000:ℝ) (574101/2500:ℝ) (500/11280461:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 2 12 2229049 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h138 using 1 <;> norm_num
    · norm_num
  have h140 : rootPrefix F 2512225≤(292829/1250:ℝ)+(200/4650073:ℝ)*thetaPrefix F 2512225 := by
    apply root_prefix_step F hprime 2365444 2512225 (29338/2000) (574101/2500:ℝ) (292829/1250:ℝ) (200/4650073:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 18 2 2365444 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h139 using 1 <;> norm_num
    · norm_num
  have h141 : rootPrefix F 2666689≤(2402059/10000:ℝ)+(200/4828781:ℝ)*thetaPrefix F 2666689 := by
    apply root_prefix_step F hprime 2512225 2666689 (29338/2000) (292829/1250:ℝ) (2402059/10000:ℝ) (200/4828781:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 18 2 2512225 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h140 using 1 <;> norm_num
    · norm_num
  have h142 : rootPrefix F 2829124≤(48997/200:ℝ)+(100/2486837:ℝ)*thetaPrefix F 2829124 := by
    apply root_prefix_step F hprime 2666689 2829124 (29570/2000) (2402059/10000:ℝ) (48997/200:ℝ) (100/2486837:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 15 4 2666689 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h141 using 1 <;> norm_num
    · norm_num
  have h143 : rootPrefix F 3003289≤(1256191/5000:ℝ)+(1000/25823433:ℝ)*thetaPrefix F 3003289 := by
    apply root_prefix_step F hprime 2829124 3003289 (29570/2000) (48997/200:ℝ) (1256191/5000:ℝ) (1000/25823433:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 15 4 2829124 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h142 using 1 <;> norm_num
    · norm_num
  have h144 : rootPrefix F 3186225≤(2569039/10000:ℝ)+(80/2135931:ℝ)*thetaPrefix F 3186225 := by
    apply root_prefix_step F hprime 3003289 3186225 (29802/2000) (1256191/5000:ℝ) (2569039/10000:ℝ) (80/2135931:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 12 6 3003289 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h143 using 1 <;> norm_num
    · norm_num
  have h145 : rootPrefix F 3381921≤(656983/2500:ℝ)+(1000/27616263:ℝ)*thetaPrefix F 3381921 := by
    apply root_prefix_step F hprime 3186225 3381921 (29915/2000) (2569039/10000:ℝ) (656983/2500:ℝ) (1000/27616263:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 20 1 3186225 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h144 using 1 <;> norm_num
    · norm_num
  have h146 : rootPrefix F 3591025≤(168022/625:ℝ)+(400/11425713:ℝ)*thetaPrefix F 3591025 := by
    apply root_prefix_step F hprime 3381921 3591025 (30034/2000) (656983/2500:ℝ) (168022/625:ℝ) (400/11425713:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 9 8 3381921 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h145 using 1 <;> norm_num
    · norm_num
  have h147 : rootPrefix F 3810304≤(1375007/5000:ℝ)+(125/3692452:ℝ)*thetaPrefix F 3810304 := by
    apply root_prefix_step F hprime 3591025 3810304 (30147/2000) (168022/625:ℝ) (1375007/5000:ℝ) (125/3692452:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 17 3 3591025 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h146 using 1 <;> norm_num
    · norm_num
  have h148 : rootPrefix F 4000000≤(2322887/5000:ℝ)+(0:ℝ)*thetaPrefix F 4000000 := by
    apply root_prefix_step F hprime 3810304 4000000 (30266/2000) (1375007/5000:ℝ) (2322887/5000:ℝ) (0:ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      (by convert mixed_log_lower 6 10 3810304 (by norm_num) using 1 <;> norm_num)
      (by norm_num)
    · convert h147 using 1 <;> norm_num
    · norm_num
  have hf : F.filter (fun p => p≤4000000)=F := filter_eq_self.mpr (fun p hp => (hF p hp).2)
  simp only [zero_mul,add_zero,rootPrefix,hf] at h148
  exact h148.trans (by norm_num)

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
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 465 := by
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
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*v d) ≤ exp 476 := by
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
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 465 ∧
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*AnalyticNumberTheory.Sieve.goldbachNu d) ≤ exp 476 := by
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
end ChenEffective.GRH122
end
