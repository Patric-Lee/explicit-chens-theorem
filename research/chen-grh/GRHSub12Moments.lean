import GRHMomentCounts
import GRHMomentCountSoundness
import GRH122Moments

/-! Certified prime-count moments for the complete H < 12 route. -/
noncomputable section
namespace ChenEffective.GRHSub12
open Real Finset
open ChenEffective.GRH125 (rootPrefix root_prefix_small)
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
set_option maxErrors 100

theorem root_prefix_count_step (F : Finset ℕ) (hF : ∀ p∈F,p.Prime)
    (r b lo w B count : ℕ) (c C : ℝ)
    (hr : 0<r) (hr2 : 2≤ r^2) (hab : r^2≤ b)
    (hal : r^2<lo) (hla : lo≤ r^2+2) (hlo : lo%2=1) (hlo3 : 3≤ lo)
    (hb : b<lo+2*(2^w*B)) (htop : lo+2*(2^w*B)-1≤ PsiFinite.baseCover)
    (Y : ℕ) (hcert : Nat.beq (PlattWindow.segmentCounts lo w B) Y=true)
    (hsum : Nat.beq (sumFields w Y B) count=true)
    (hprev : rootPrefix F (r^2)≤ c) (hpay : c+(count:ℝ)/r≤ C) :
    rootPrefix F b≤ C := by
  have hi := prime_root_interval_count F hF r b lo w B count hr hr2 hal hla hlo hlo3 hb htop Y hcert hsum
  have hsplit : rootPrefix F b=rootPrefix F (r^2)+
      (∑ p∈F.filter (fun p=>r^2<p ∧ p≤ b),1/sqrt (p:ℝ)) := by
    simp only [rootPrefix,sum_filter]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> first | omega | ring
  linarith only [hi,hsplit,hprev,hpay]

theorem prime_root_moment (F : Finset ℕ)
    (hF : ∀ p∈F,p.Prime ∧ p≤4000000) :
    (∑ p∈F,1/sqrt (p:ℝ))≤340 := by
  classical
  have hprime : ∀ p∈F,p.Prime := fun p hp => (hF p hp).1
  have h0 : rootPrefix F 100≤20 := root_prefix_small F hprime
  have h1 : rootPrefix F 121≤(207/10:ℝ) := by
    apply root_prefix_count_step F hprime 10 121 101 4 1 7 (20:ℝ) (207/10:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B000.packed MomentCertificates.B000.count_checked MomentCertificates.B000.sum_checked
    · convert h0 using 1 <;> norm_num
    · norm_num
  have h2 : rootPrefix F 144≤(42491/2000:ℝ) := by
    apply root_prefix_count_step F hprime 11 144 123 4 1 6 (207/10:ℝ) (42491/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B001.packed MomentCertificates.B001.count_checked MomentCertificates.B001.sum_checked
    · convert h1 using 1 <;> norm_num
    · norm_num
  have h3 : rootPrefix F 169≤(43491/2000:ℝ) := by
    apply root_prefix_count_step F hprime 12 169 145 4 1 6 (42491/2000:ℝ) (43491/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B002.packed MomentCertificates.B002.count_checked MomentCertificates.B002.sum_checked
    · convert h2 using 1 <;> norm_num
    · norm_num
  have h4 : rootPrefix F 196≤(5571/250:ℝ) := by
    apply root_prefix_count_step F hprime 13 196 171 4 1 7 (43491/2000:ℝ) (5571/250:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B003.packed MomentCertificates.B003.count_checked MomentCertificates.B003.sum_checked
    · convert h3 using 1 <;> norm_num
    · norm_num
  have h5 : rootPrefix F 225≤(56603/2500:ℝ) := by
    apply root_prefix_count_step F hprime 14 225 197 4 1 5 (5571/250:ℝ) (56603/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B004.packed MomentCertificates.B004.count_checked MomentCertificates.B004.sum_checked
    · convert h4 using 1 <;> norm_num
    · norm_num
  have h6 : rootPrefix F 256≤(231079/10000:ℝ) := by
    apply root_prefix_count_step F hprime 15 256 227 4 1 7 (56603/2500:ℝ) (231079/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B005.packed MomentCertificates.B005.count_checked MomentCertificates.B005.sum_checked
    · convert h5 using 1 <;> norm_num
    · norm_num
  have h7 : rootPrefix F 289≤(238579/10000:ℝ) := by
    apply root_prefix_count_step F hprime 16 289 257 4 2 12 (231079/10000:ℝ) (238579/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B006.packed MomentCertificates.B006.count_checked MomentCertificates.B006.sum_checked
    · convert h6 using 1 <;> norm_num
    · norm_num
  have h8 : rootPrefix F 324≤(122231/5000:ℝ) := by
    apply root_prefix_count_step F hprime 17 324 291 4 2 10 (238579/10000:ℝ) (122231/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B007.packed MomentCertificates.B007.count_checked MomentCertificates.B007.sum_checked
    · convert h7 using 1 <;> norm_num
    · norm_num
  have h9 : rootPrefix F 361≤(125009/5000:ℝ) := by
    apply root_prefix_count_step F hprime 18 361 325 4 2 10 (122231/5000:ℝ) (125009/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B008.packed MomentCertificates.B008.count_checked MomentCertificates.B008.sum_checked
    · convert h8 using 1 <;> norm_num
    · norm_num
  have h10 : rootPrefix F 400≤(127641/5000:ℝ) := by
    apply root_prefix_count_step F hprime 19 400 363 4 2 10 (125009/5000:ℝ) (127641/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B009.packed MomentCertificates.B009.count_checked MomentCertificates.B009.sum_checked
    · convert h9 using 1 <;> norm_num
    · norm_num
  have h11 : rootPrefix F 441≤(130641/5000:ℝ) := by
    apply root_prefix_count_step F hprime 20 441 401 4 2 12 (127641/5000:ℝ) (130641/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B010.packed MomentCertificates.B010.count_checked MomentCertificates.B010.sum_checked
    · convert h10 using 1 <;> norm_num
    · norm_num
  have h12 : rootPrefix F 484≤(266521/10000:ℝ) := by
    apply root_prefix_count_step F hprime 21 484 443 4 2 11 (130641/5000:ℝ) (266521/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B011.packed MomentCertificates.B011.count_checked MomentCertificates.B011.sum_checked
    · convert h11 using 1 <;> norm_num
    · norm_num
  have h13 : rootPrefix F 529≤(67653/2500:ℝ) := by
    apply root_prefix_count_step F hprime 22 529 485 4 2 9 (266521/10000:ℝ) (67653/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B012.packed MomentCertificates.B012.count_checked MomentCertificates.B012.sum_checked
    · convert h12 using 1 <;> norm_num
    · norm_num
  have h14 : rootPrefix F 576≤(137263/5000:ℝ) := by
    apply root_prefix_count_step F hprime 23 576 531 4 2 9 (67653/2500:ℝ) (137263/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B013.packed MomentCertificates.B013.count_checked MomentCertificates.B013.sum_checked
    · convert h13 using 1 <;> norm_num
    · norm_num
  have h15 : rootPrefix F 625≤(278693/10000:ℝ) := by
    apply root_prefix_count_step F hprime 24 625 577 4 2 10 (137263/5000:ℝ) (278693/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B014.packed MomentCertificates.B014.count_checked MomentCertificates.B014.sum_checked
    · convert h14 using 1 <;> norm_num
    · norm_num
  have h16 : rootPrefix F 676≤(282693/10000:ℝ) := by
    apply root_prefix_count_step F hprime 25 676 627 4 2 10 (278693/10000:ℝ) (282693/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B015.packed MomentCertificates.B015.count_checked MomentCertificates.B015.sum_checked
    · convert h15 using 1 <;> norm_num
    · norm_num
  have h17 : rootPrefix F 729≤(57231/2000:ℝ) := by
    apply root_prefix_count_step F hprime 26 729 677 4 2 9 (282693/10000:ℝ) (57231/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B016.packed MomentCertificates.B016.count_checked MomentCertificates.B016.sum_checked
    · convert h16 using 1 <;> norm_num
    · norm_num
  have h18 : rootPrefix F 784≤(289489/10000:ℝ) := by
    apply root_prefix_count_step F hprime 27 784 731 4 2 9 (57231/2000:ℝ) (289489/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B017.packed MomentCertificates.B017.count_checked MomentCertificates.B017.sum_checked
    · convert h17 using 1 <;> norm_num
    · norm_num
  have h19 : rootPrefix F 841≤(18294/625:ℝ) := by
    apply root_prefix_count_step F hprime 28 841 785 4 2 9 (289489/10000:ℝ) (18294/625:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B018.packed MomentCertificates.B018.count_checked MomentCertificates.B018.sum_checked
    · convert h18 using 1 <;> norm_num
    · norm_num
  have h20 : rootPrefix F 900≤(295463/10000:ℝ) := by
    apply root_prefix_count_step F hprime 29 900 843 4 2 8 (18294/625:ℝ) (295463/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B019.packed MomentCertificates.B019.count_checked MomentCertificates.B019.sum_checked
    · convert h19 using 1 <;> norm_num
    · norm_num
  have h21 : rootPrefix F 961≤(29813/1000:ℝ) := by
    apply root_prefix_count_step F hprime 30 961 901 4 2 8 (295463/10000:ℝ) (29813/1000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B020.packed MomentCertificates.B020.count_checked MomentCertificates.B020.sum_checked
    · convert h20 using 1 <;> norm_num
    · norm_num
  have h22 : rootPrefix F 1024≤(75339/2500:ℝ) := by
    apply root_prefix_count_step F hprime 31 1024 963 4 2 10 (29813/1000:ℝ) (75339/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B021.packed MomentCertificates.B021.count_checked MomentCertificates.B021.sum_checked
    · convert h21 using 1 <;> norm_num
    · norm_num
  have h23 : rootPrefix F 1089≤(76511/2500:ℝ) := by
    apply root_prefix_count_step F hprime 32 1089 1025 4 3 15 (75339/2500:ℝ) (76511/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B022.packed MomentCertificates.B022.count_checked MomentCertificates.B022.sum_checked
    · convert h22 using 1 <;> norm_num
    · norm_num
  have h24 : rootPrefix F 1156≤(19374/625:ℝ) := by
    apply root_prefix_count_step F hprime 33 1156 1091 4 3 13 (76511/2500:ℝ) (19374/625:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B023.packed MomentCertificates.B023.count_checked MomentCertificates.B023.sum_checked
    · convert h23 using 1 <;> norm_num
    · norm_num
  have h25 : rootPrefix F 1296≤(316749/10000:ℝ) := by
    apply root_prefix_count_step F hprime 34 1296 1157 4 5 23 (19374/625:ℝ) (316749/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B024.packed MomentCertificates.B024.count_checked MomentCertificates.B024.sum_checked
    · convert h24 using 1 <;> norm_num
    · norm_num
  have h26 : rootPrefix F 1444≤(322583/10000:ℝ) := by
    apply root_prefix_count_step F hprime 36 1444 1297 4 5 21 (316749/10000:ℝ) (322583/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B025.packed MomentCertificates.B025.count_checked MomentCertificates.B025.sum_checked
    · convert h25 using 1 <;> norm_num
    · norm_num
  have h27 : rootPrefix F 1600≤(328899/10000:ℝ) := by
    apply root_prefix_count_step F hprime 38 1600 1445 4 5 24 (322583/10000:ℝ) (328899/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B026.packed MomentCertificates.B026.count_checked MomentCertificates.B026.sum_checked
    · convert h26 using 1 <;> norm_num
    · norm_num
  have h28 : rootPrefix F 1764≤(335649/10000:ℝ) := by
    apply root_prefix_count_step F hprime 40 1764 1601 4 6 27 (328899/10000:ℝ) (335649/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B027.packed MomentCertificates.B027.count_checked MomentCertificates.B027.sum_checked
    · convert h27 using 1 <;> norm_num
    · norm_num
  have h29 : rootPrefix F 1936≤(170563/5000:ℝ) := by
    apply root_prefix_count_step F hprime 42 1936 1765 4 6 23 (335649/10000:ℝ) (170563/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B028.packed MomentCertificates.B028.count_checked MomentCertificates.B028.sum_checked
    · convert h28 using 1 <;> norm_num
    · norm_num
  have h30 : rootPrefix F 2116≤(346581/10000:ℝ) := by
    apply root_prefix_count_step F hprime 44 2116 1937 4 6 24 (170563/5000:ℝ) (346581/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B029.packed MomentCertificates.B029.count_checked MomentCertificates.B029.sum_checked
    · convert h29 using 1 <;> norm_num
    · norm_num
  have h31 : rootPrefix F 2304≤(351581/10000:ℝ) := by
    apply root_prefix_count_step F hprime 46 2304 2117 4 6 23 (346581/10000:ℝ) (351581/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B030.packed MomentCertificates.B030.count_checked MomentCertificates.B030.sum_checked
    · convert h30 using 1 <;> norm_num
    · norm_num
  have h32 : rootPrefix F 2500≤(178603/5000:ℝ) := by
    apply root_prefix_count_step F hprime 48 2500 2305 4 7 27 (351581/10000:ℝ) (178603/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B031.packed MomentCertificates.B031.count_checked MomentCertificates.B031.sum_checked
    · convert h31 using 1 <;> norm_num
    · norm_num
  have h33 : rootPrefix F 2704≤(181603/5000:ℝ) := by
    apply root_prefix_count_step F hprime 50 2704 2501 4 7 30 (178603/5000:ℝ) (181603/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B032.packed MomentCertificates.B032.count_checked MomentCertificates.B032.sum_checked
    · convert h32 using 1 <;> norm_num
    · norm_num
  have h34 : rootPrefix F 2916≤(23061/625:ℝ) := by
    apply root_prefix_count_step F hprime 52 2916 2705 4 7 30 (181603/5000:ℝ) (23061/625:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B033.packed MomentCertificates.B033.count_checked MomentCertificates.B033.sum_checked
    · convert h33 using 1 <;> norm_num
    · norm_num
  have h35 : rootPrefix F 3136≤(186803/5000:ℝ) := by
    apply root_prefix_count_step F hprime 54 3136 2917 4 7 25 (23061/625:ℝ) (186803/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B034.packed MomentCertificates.B034.count_checked MomentCertificates.B034.sum_checked
    · convert h34 using 1 <;> norm_num
    · norm_num
  have h36 : rootPrefix F 3364≤(379499/10000:ℝ) := by
    apply root_prefix_count_step F hprime 56 3364 3137 4 8 33 (186803/5000:ℝ) (379499/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B035.packed MomentCertificates.B035.count_checked MomentCertificates.B035.sum_checked
    · convert h35 using 1 <;> norm_num
    · norm_num
  have h37 : rootPrefix F 3600≤(385017/10000:ℝ) := by
    apply root_prefix_count_step F hprime 58 3600 3365 4 8 32 (379499/10000:ℝ) (385017/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B036.packed MomentCertificates.B036.count_checked MomentCertificates.B036.sum_checked
    · convert h36 using 1 <;> norm_num
    · norm_num
  have h38 : rootPrefix F 3844≤(390351/10000:ℝ) := by
    apply root_prefix_count_step F hprime 60 3844 3601 4 8 32 (385017/10000:ℝ) (390351/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B037.packed MomentCertificates.B037.count_checked MomentCertificates.B037.sum_checked
    · convert h37 using 1 <;> norm_num
    · norm_num
  have h39 : rootPrefix F 4096≤(197837/5000:ℝ) := by
    apply root_prefix_count_step F hprime 62 4096 3845 4 8 33 (390351/10000:ℝ) (197837/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B038.packed MomentCertificates.B038.count_checked MomentCertificates.B038.sum_checked
    · convert h38 using 1 <;> norm_num
    · norm_num
  have h40 : rootPrefix F 4356≤(400831/10000:ℝ) := by
    apply root_prefix_count_step F hprime 64 4356 4097 4 9 33 (197837/5000:ℝ) (400831/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B039.packed MomentCertificates.B039.count_checked MomentCertificates.B039.sum_checked
    · convert h39 using 1 <;> norm_num
    · norm_num
  have h41 : rootPrefix F 4624≤(405831/10000:ℝ) := by
    apply root_prefix_count_step F hprime 66 4624 4357 4 9 33 (400831/10000:ℝ) (405831/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B040.packed MomentCertificates.B040.count_checked MomentCertificates.B040.sum_checked
    · convert h40 using 1 <;> norm_num
    · norm_num
  have h42 : rootPrefix F 5041≤(206813/5000:ℝ) := by
    apply root_prefix_count_step F hprime 68 5041 4625 4 14 53 (405831/10000:ℝ) (206813/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B041.packed MomentCertificates.B041.count_checked MomentCertificates.B041.sum_checked
    · convert h41 using 1 <;> norm_num
    · norm_num
  have h43 : rootPrefix F 5476≤(420669/10000:ℝ) := by
    apply root_prefix_count_step F hprime 71 5476 5043 4 14 50 (206813/5000:ℝ) (420669/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B042.packed MomentCertificates.B042.count_checked MomentCertificates.B042.sum_checked
    · convert h42 using 1 <;> norm_num
    · norm_num
  have h44 : rootPrefix F 5929≤(214321/5000:ℝ) := by
    apply root_prefix_count_step F hprime 74 5929 5477 4 15 59 (420669/10000:ℝ) (214321/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B043.packed MomentCertificates.B043.count_checked MomentCertificates.B043.sum_checked
    · convert h43 using 1 <;> norm_num
    · norm_num
  have h45 : rootPrefix F 6400≤(87157/2000:ℝ) := by
    apply root_prefix_count_step F hprime 77 6400 5931 4 15 55 (214321/5000:ℝ) (87157/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B044.packed MomentCertificates.B044.count_checked MomentCertificates.B044.sum_checked
    · convert h44 using 1 <;> norm_num
    · norm_num
  have h46 : rootPrefix F 6889≤(22133/500:ℝ) := by
    apply root_prefix_count_step F hprime 80 6889 6401 4 16 55 (87157/2000:ℝ) (22133/500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B045.packed MomentCertificates.B045.count_checked MomentCertificates.B045.sum_checked
    · convert h45 using 1 <;> norm_num
    · norm_num
  have h47 : rootPrefix F 7396≤(224523/5000:ℝ) := by
    apply root_prefix_count_step F hprime 83 7396 6891 4 16 53 (22133/500:ℝ) (224523/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B046.packed MomentCertificates.B046.count_checked MomentCertificates.B046.sum_checked
    · convert h46 using 1 <;> norm_num
    · norm_num
  have h48 : rootPrefix F 7921≤(57061/1250:ℝ) := by
    apply root_prefix_count_step F hprime 86 7921 7397 4 17 64 (224523/5000:ℝ) (57061/1250:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B047.packed MomentCertificates.B047.count_checked MomentCertificates.B047.sum_checked
    · convert h47 using 1 <;> norm_num
    · norm_num
  have h49 : rootPrefix F 8464≤(92601/2000:ℝ) := by
    apply root_prefix_count_step F hprime 89 8464 7923 4 17 58 (57061/1250:ℝ) (92601/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B048.packed MomentCertificates.B048.count_checked MomentCertificates.B048.sum_checked
    · convert h48 using 1 <;> norm_num
    · norm_num
  have h50 : rootPrefix F 9025≤(234981/5000:ℝ) := by
    apply root_prefix_count_step F hprime 92 9025 8465 4 18 64 (92601/2000:ℝ) (234981/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B049.packed MomentCertificates.B049.count_checked MomentCertificates.B049.sum_checked
    · convert h49 using 1 <;> norm_num
    · norm_num
  have h51 : rootPrefix F 9604≤(238613/5000:ℝ) := by
    apply root_prefix_count_step F hprime 95 9604 9027 4 19 69 (234981/5000:ℝ) (238613/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B050.packed MomentCertificates.B050.count_checked MomentCertificates.B050.sum_checked
    · convert h50 using 1 <;> norm_num
    · norm_num
  have h52 : rootPrefix F 10201≤(96833/2000:ℝ) := by
    apply root_prefix_count_step F hprime 98 10201 9605 4 19 68 (238613/5000:ℝ) (96833/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B051.packed MomentCertificates.B051.count_checked MomentCertificates.B051.sum_checked
    · convert h51 using 1 <;> norm_num
    · norm_num
  have h53 : rootPrefix F 11025≤(492581/10000:ℝ) := by
    apply root_prefix_count_step F hprime 101 11025 10203 4 26 85 (96833/2000:ℝ) (492581/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B052.packed MomentCertificates.B052.count_checked MomentCertificates.B052.sum_checked
    · convert h52 using 1 <;> norm_num
    · norm_num
  have h54 : rootPrefix F 11881≤(250481/5000:ℝ) := by
    apply root_prefix_count_step F hprime 105 11881 11027 4 27 88 (492581/10000:ℝ) (250481/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B053.packed MomentCertificates.B053.count_checked MomentCertificates.B053.sum_checked
    · convert h53 using 1 <;> norm_num
    · norm_num
  have h55 : rootPrefix F 12769≤(510137/10000:ℝ) := by
    apply root_prefix_count_step F hprime 109 12769 11883 4 28 100 (250481/5000:ℝ) (510137/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B054.packed MomentCertificates.B054.count_checked MomentCertificates.B054.sum_checked
    · convert h54 using 1 <;> norm_num
    · norm_num
  have h56 : rootPrefix F 13689≤(259361/5000:ℝ) := by
    apply root_prefix_count_step F hprime 113 13689 12771 4 29 97 (510137/10000:ℝ) (259361/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B055.packed MomentCertificates.B055.count_checked MomentCertificates.B055.sum_checked
    · convert h55 using 1 <;> norm_num
    · norm_num
  have h57 : rootPrefix F 14641≤(527099/10000:ℝ) := by
    apply root_prefix_count_step F hprime 117 14641 13691 4 30 98 (259361/5000:ℝ) (527099/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B056.packed MomentCertificates.B056.count_checked MomentCertificates.B056.sum_checked
    · convert h56 using 1 <;> norm_num
    · norm_num
  have h58 : rootPrefix F 15625≤(267971/5000:ℝ) := by
    apply root_prefix_count_step F hprime 121 15625 14643 4 31 107 (527099/10000:ℝ) (267971/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B057.packed MomentCertificates.B057.count_checked MomentCertificates.B057.sum_checked
    · convert h57 using 1 <;> norm_num
    · norm_num
  have h59 : rootPrefix F 16641≤(272131/5000:ℝ) := by
    apply root_prefix_count_step F hprime 125 16641 15627 4 32 104 (267971/5000:ℝ) (272131/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B058.packed MomentCertificates.B058.count_checked MomentCertificates.B058.sum_checked
    · convert h58 using 1 <;> norm_num
    · norm_num
  have h60 : rootPrefix F 17689≤(110527/2000:ℝ) := by
    apply root_prefix_count_step F hprime 129 17689 16643 4 33 108 (272131/5000:ℝ) (110527/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B059.packed MomentCertificates.B059.count_checked MomentCertificates.B059.sum_checked
    · convert h59 using 1 <;> norm_num
    · norm_num
  have h61 : rootPrefix F 18769≤(280453/5000:ℝ) := by
    apply root_prefix_count_step F hprime 133 18769 17691 4 34 110 (110527/2000:ℝ) (280453/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B060.packed MomentCertificates.B060.count_checked MomentCertificates.B060.sum_checked
    · convert h60 using 1 <;> norm_num
    · norm_num
  have h62 : rootPrefix F 20164≤(571271/10000:ℝ) := by
    apply root_prefix_count_step F hprime 137 20164 18771 4 44 142 (280453/5000:ℝ) (571271/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B061.packed MomentCertificates.B061.count_checked MomentCertificates.B061.sum_checked
    · convert h61 using 1 <;> norm_num
    · norm_num
  have h63 : rootPrefix F 21609≤(290847/5000:ℝ) := by
    apply root_prefix_count_step F hprime 142 21609 20165 4 46 148 (571271/10000:ℝ) (290847/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B062.packed MomentCertificates.B062.count_checked MomentCertificates.B062.sum_checked
    · convert h62 using 1 <;> norm_num
    · norm_num
  have h64 : rootPrefix F 23104≤(592171/10000:ℝ) := by
    apply root_prefix_count_step F hprime 147 23104 21611 4 47 154 (290847/5000:ℝ) (592171/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B063.packed MomentCertificates.B063.count_checked MomentCertificates.B063.sum_checked
    · convert h63 using 1 <;> norm_num
    · norm_num
  have h65 : rootPrefix F 24649≤(301053/5000:ℝ) := by
    apply root_prefix_count_step F hprime 152 24649 23105 4 49 151 (592171/10000:ℝ) (301053/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B064.packed MomentCertificates.B064.count_checked MomentCertificates.B064.sum_checked
    · convert h64 using 1 <;> norm_num
    · norm_num
  have h66 : rootPrefix F 26244≤(611979/10000:ℝ) := by
    apply root_prefix_count_step F hprime 157 26244 24651 4 50 155 (301053/5000:ℝ) (611979/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B065.packed MomentCertificates.B065.count_checked MomentCertificates.B065.sum_checked
    · convert h65 using 1 <;> norm_num
    · norm_num
  have h67 : rootPrefix F 27889≤(621979/10000:ℝ) := by
    apply root_prefix_count_step F hprime 162 27889 26245 4 52 162 (611979/10000:ℝ) (621979/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B066.packed MomentCertificates.B066.count_checked MomentCertificates.B066.sum_checked
    · convert h66 using 1 <;> norm_num
    · norm_num
  have h68 : rootPrefix F 29929≤(158459/2500:ℝ) := by
    apply root_prefix_count_step F hprime 167 29929 27891 4 64 198 (621979/10000:ℝ) (158459/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B067.packed MomentCertificates.B067.count_checked MomentCertificates.B067.sum_checked
    · convert h67 using 1 <;> norm_num
    · norm_num
  have h69 : rootPrefix F 32041≤(161277/2500:ℝ) := by
    apply root_prefix_count_step F hprime 173 32041 29931 4 66 195 (158459/2500:ℝ) (161277/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B068.packed MomentCertificates.B068.count_checked MomentCertificates.B068.sum_checked
    · convert h68 using 1 <;> norm_num
    · norm_num
  have h70 : rootPrefix F 34225≤(131491/2000:ℝ) := by
    apply root_prefix_count_step F hprime 179 34225 32043 4 69 221 (161277/2500:ℝ) (131491/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B069.packed MomentCertificates.B069.count_checked MomentCertificates.B069.sum_checked
    · convert h69 using 1 <;> norm_num
    · norm_num
  have h71 : rootPrefix F 36481≤(669023/10000:ℝ) := by
    apply root_prefix_count_step F hprime 185 36481 34227 4 71 214 (131491/2000:ℝ) (669023/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B070.packed MomentCertificates.B070.count_checked MomentCertificates.B070.sum_checked
    · convert h70 using 1 <;> norm_num
    · norm_num
  have h72 : rootPrefix F 38809≤(340297/5000:ℝ) := by
    apply root_prefix_count_step F hprime 191 38809 36483 4 73 221 (669023/10000:ℝ) (340297/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B071.packed MomentCertificates.B071.count_checked MomentCertificates.B071.sum_checked
    · convert h71 using 1 <;> norm_num
    · norm_num
  have h73 : rootPrefix F 41209≤(138393/2000:ℝ) := by
    apply root_prefix_count_step F hprime 197 41209 38811 4 75 224 (340297/5000:ℝ) (138393/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B072.packed MomentCertificates.B072.count_checked MomentCertificates.B072.sum_checked
    · convert h72 using 1 <;> norm_num
    · norm_num
  have h74 : rootPrefix F 44100≤(705709/10000:ℝ) := by
    apply root_prefix_count_step F hprime 203 44100 41211 4 91 279 (138393/2000:ℝ) (705709/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B073.packed MomentCertificates.B073.count_checked MomentCertificates.B073.sum_checked
    · convert h73 using 1 <;> norm_num
    · norm_num
  have h75 : rootPrefix F 47089≤(718519/10000:ℝ) := by
    apply root_prefix_count_step F hprime 210 47089 44101 4 94 269 (705709/10000:ℝ) (718519/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B074.packed MomentCertificates.B074.count_checked MomentCertificates.B074.sum_checked
    · convert h74 using 1 <;> norm_num
    · norm_num
  have h76 : rootPrefix F 50176≤(9152/125:ℝ) := by
    apply root_prefix_count_step F hprime 217 50176 47091 4 97 296 (718519/10000:ℝ) (9152/125:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B075.packed MomentCertificates.B075.count_checked MomentCertificates.B075.sum_checked
    · convert h75 using 1 <;> norm_num
    · norm_num
  have h77 : rootPrefix F 53361≤(745107/10000:ℝ) := by
    apply root_prefix_count_step F hprime 224 53361 50177 4 100 290 (9152/125:ℝ) (745107/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B076.packed MomentCertificates.B076.count_checked MomentCertificates.B076.sum_checked
    · convert h76 using 1 <;> norm_num
    · norm_num
  have h78 : rootPrefix F 56644≤(379069/5000:ℝ) := by
    apply root_prefix_count_step F hprime 231 56644 53363 4 103 301 (745107/10000:ℝ) (379069/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B077.packed MomentCertificates.B077.count_checked MomentCertificates.B077.sum_checked
    · convert h77 using 1 <;> norm_num
    · norm_num
  have h79 : rootPrefix F 60516≤(773181/10000:ℝ) := by
    apply root_prefix_count_step F hprime 238 60516 56645 4 121 358 (379069/5000:ℝ) (773181/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B078.packed MomentCertificates.B078.count_checked MomentCertificates.B078.sum_checked
    · convert h78 using 1 <;> norm_num
    · norm_num
  have h80 : rootPrefix F 64516≤(787531/10000:ℝ) := by
    apply root_prefix_count_step F hprime 246 64516 60517 4 125 353 (773181/10000:ℝ) (787531/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B079.packed MomentCertificates.B079.count_checked MomentCertificates.B079.sum_checked
    · convert h79 using 1 <;> norm_num
    · norm_num
  have h81 : rootPrefix F 68644≤(802059/10000:ℝ) := by
    apply root_prefix_count_step F hprime 254 68644 64517 4 129 369 (787531/10000:ℝ) (802059/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B080.packed MomentCertificates.B080.count_checked MomentCertificates.B080.sum_checked
    · convert h80 using 1 <;> norm_num
    · norm_num
  have h82 : rootPrefix F 72900≤(408339/5000:ℝ) := by
    apply root_prefix_count_step F hprime 262 72900 68645 4 133 383 (802059/10000:ℝ) (408339/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B081.packed MomentCertificates.B081.count_checked MomentCertificates.B081.sum_checked
    · convert h81 using 1 <;> norm_num
    · norm_num
  have h83 : rootPrefix F 77841≤(20829/250:ℝ) := by
    apply root_prefix_count_step F hprime 270 77841 72901 4 155 445 (408339/5000:ℝ) (20829/250:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B082.packed MomentCertificates.B082.count_checked MomentCertificates.B082.sum_checked
    · convert h82 using 1 <;> norm_num
    · norm_num
  have h84 : rootPrefix F 82944≤(849397/10000:ℝ) := by
    apply root_prefix_count_step F hprime 279 82944 77843 4 160 453 (20829/250:ℝ) (849397/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B083.packed MomentCertificates.B083.count_checked MomentCertificates.B083.sum_checked
    · convert h83 using 1 <;> norm_num
    · norm_num
  have h85 : rootPrefix F 88209≤(865161/10000:ℝ) := by
    apply root_prefix_count_step F hprime 288 88209 82945 4 165 454 (849397/10000:ℝ) (865161/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B084.packed MomentCertificates.B084.count_checked MomentCertificates.B084.sum_checked
    · convert h84 using 1 <;> norm_num
    · norm_num
  have h86 : rootPrefix F 93636≤(881559/10000:ℝ) := by
    apply root_prefix_count_step F hprime 297 93636 88211 4 170 487 (865161/10000:ℝ) (881559/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B085.packed MomentCertificates.B085.count_checked MomentCertificates.B085.sum_checked
    · convert h85 using 1 <;> norm_num
    · norm_num
  have h87 : rootPrefix F 99856≤(899239/10000:ℝ) := by
    apply root_prefix_count_step F hprime 306 99856 93637 4 195 541 (881559/10000:ℝ) (899239/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B086.packed MomentCertificates.B086.count_checked MomentCertificates.B086.sum_checked
    · convert h86 using 1 <;> norm_num
    · norm_num
  have h88 : rootPrefix F 106276≤(916613/10000:ℝ) := by
    apply root_prefix_count_step F hprime 316 106276 99857 4 201 549 (899239/10000:ℝ) (916613/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B087.packed MomentCertificates.B087.count_checked MomentCertificates.B087.sum_checked
    · convert h87 using 1 <;> norm_num
    · norm_num
  have h89 : rootPrefix F 112896≤(933883/10000:ℝ) := by
    apply root_prefix_count_step F hprime 326 112896 106277 4 207 563 (916613/10000:ℝ) (933883/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B088.packed MomentCertificates.B088.count_checked MomentCertificates.B088.sum_checked
    · convert h88 using 1 <;> norm_num
    · norm_num
  have h90 : rootPrefix F 120409≤(95311/1000:ℝ) := by
    apply root_prefix_count_step F hprime 336 120409 112897 4 235 646 (933883/10000:ℝ) (95311/1000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B089.packed MomentCertificates.B089.count_checked MomentCertificates.B089.sum_checked
    · convert h89 using 1 <;> norm_num
    · norm_num
  have h91 : rootPrefix F 128164≤(486123/5000:ℝ) := by
    apply root_prefix_count_step F hprime 347 128164 120411 4 243 664 (95311/1000:ℝ) (486123/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B090.packed MomentCertificates.B090.count_checked MomentCertificates.B090.sum_checked
    · convert h90 using 1 <;> norm_num
    · norm_num
  have h92 : rootPrefix F 136161≤(991241/10000:ℝ) := by
    apply root_prefix_count_step F hprime 358 136161 128165 4 250 680 (486123/5000:ℝ) (991241/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B091.packed MomentCertificates.B091.count_checked MomentCertificates.B091.sum_checked
    · convert h91 using 1 <;> norm_num
    · norm_num
  have h93 : rootPrefix F 145161≤(1011811/10000:ℝ) := by
    apply root_prefix_count_step F hprime 369 145161 136163 4 282 759 (991241/10000:ℝ) (1011811/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B092.packed MomentCertificates.B092.count_checked MomentCertificates.B092.sum_checked
    · convert h92 using 1 <;> norm_num
    · norm_num
  have h94 : rootPrefix F 154449≤(1032651/10000:ℝ) := by
    apply root_prefix_count_step F hprime 381 154449 145163 4 291 794 (1011811/10000:ℝ) (1032651/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B093.packed MomentCertificates.B093.count_checked MomentCertificates.B093.sum_checked
    · convert h93 using 1 <;> norm_num
    · norm_num
  have h95 : rootPrefix F 164025≤(1052779/10000:ℝ) := by
    apply root_prefix_count_step F hprime 393 164025 154451 4 300 791 (1032651/10000:ℝ) (1052779/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B094.packed MomentCertificates.B094.count_checked MomentCertificates.B094.sum_checked
    · convert h94 using 1 <;> norm_num
    · norm_num
  have h96 : rootPrefix F 174724≤(537217/5000:ℝ) := by
    apply root_prefix_count_step F hprime 405 174724 164027 4 335 877 (1052779/10000:ℝ) (537217/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B095.packed MomentCertificates.B095.count_checked MomentCertificates.B095.sum_checked
    · convert h95 using 1 <;> norm_num
    · norm_num
  have h97 : rootPrefix F 185761≤(54821/500:ℝ) := by
    apply root_prefix_count_step F hprime 418 185761 174725 4 345 919 (537217/5000:ℝ) (54821/500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B096.packed MomentCertificates.B096.count_checked MomentCertificates.B096.sum_checked
    · convert h96 using 1 <;> norm_num
    · norm_num
  have h98 : rootPrefix F 197136≤(559057/5000:ℝ) := by
    apply root_prefix_count_step F hprime 431 197136 185763 4 356 935 (54821/500:ℝ) (559057/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B097.packed MomentCertificates.B097.count_checked MomentCertificates.B097.sum_checked
    · convert h97 using 1 <;> norm_num
    · norm_num
  have h99 : rootPrefix F 209764≤(570769/5000:ℝ) := by
    apply root_prefix_count_step F hprime 444 209764 197137 4 395 1040 (559057/5000:ℝ) (570769/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B098.packed MomentCertificates.B098.count_checked MomentCertificates.B098.sum_checked
    · convert h98 using 1 <;> norm_num
    · norm_num
  have h100 : rootPrefix F 222784≤(116453/1000:ℝ) := by
    apply root_prefix_count_step F hprime 458 222784 209765 4 407 1053 (570769/5000:ℝ) (116453/1000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B099.packed MomentCertificates.B099.count_checked MomentCertificates.B099.sum_checked
    · convert h99 using 1 <;> norm_num
    · norm_num
  have h101 : rootPrefix F 237169≤(118917/1000:ℝ) := by
    apply root_prefix_count_step F hprime 472 237169 222785 4 450 1163 (116453/1000:ℝ) (118917/1000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B100.packed MomentCertificates.B100.count_checked MomentCertificates.B100.sum_checked
    · convert h100 using 1 <;> norm_num
    · norm_num
  have h102 : rootPrefix F 252004≤(303499/2500:ℝ) := by
    apply root_prefix_count_step F hprime 487 252004 237171 4 464 1209 (118917/1000:ℝ) (303499/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B101.packed MomentCertificates.B101.count_checked MomentCertificates.B101.sum_checked
    · convert h101 using 1 <;> norm_num
    · norm_num
  have h103 : rootPrefix F 268324≤(77502/625:ℝ) := by
    apply root_prefix_count_step F hprime 502 268324 252005 4 510 1307 (303499/2500:ℝ) (77502/625:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B102.packed MomentCertificates.B102.count_checked MomentCertificates.B102.sum_checked
    · convert h102 using 1 <;> norm_num
    · norm_num
  have h104 : rootPrefix F 285156≤(632999/5000:ℝ) := by
    apply root_prefix_count_step F hprime 518 285156 268325 4 526 1345 (77502/625:ℝ) (632999/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B103.packed MomentCertificates.B103.count_checked MomentCertificates.B103.sum_checked
    · convert h103 using 1 <;> norm_num
    · norm_num
  have h105 : rootPrefix F 303601≤(1292909/10000:ℝ) := by
    apply root_prefix_count_step F hprime 534 303601 285157 4 577 1437 (632999/5000:ℝ) (1292909/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B104.packed MomentCertificates.B104.count_checked MomentCertificates.B104.sum_checked
    · convert h104 using 1 <;> norm_num
    · norm_num
  have h106 : rootPrefix F 322624≤(330183/2500:ℝ) := by
    apply root_prefix_count_step F hprime 551 322624 303603 4 595 1533 (1292909/10000:ℝ) (330183/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B105.packed MomentCertificates.B105.count_checked MomentCertificates.B105.sum_checked
    · convert h105 using 1 <;> norm_num
    · norm_num
  have h107 : rootPrefix F 343396≤(269907/2000:ℝ) := by
    apply root_prefix_count_step F hprime 568 343396 322625 4 650 1636 (330183/2500:ℝ) (269907/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B106.packed MomentCertificates.B106.count_checked MomentCertificates.B106.sum_checked
    · convert h106 using 1 <;> norm_num
    · norm_num
  have h108 : rootPrefix F 364816≤(275617/2000:ℝ) := by
    apply root_prefix_count_step F hprime 586 364816 343397 4 670 1673 (269907/2000:ℝ) (275617/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B107.packed MomentCertificates.B107.count_checked MomentCertificates.B107.sum_checked
    · convert h107 using 1 <;> norm_num
    · norm_num
  have h109 : rootPrefix F 388129≤(703877/5000:ℝ) := by
    apply root_prefix_count_step F hprime 604 388129 364817 4 729 1792 (275617/2000:ℝ) (703877/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B108.packed MomentCertificates.B108.count_checked MomentCertificates.B108.sum_checked
    · convert h108 using 1 <;> norm_num
    · norm_num
  have h110 : rootPrefix F 412164≤(1437819/10000:ℝ) := by
    apply root_prefix_count_step F hprime 623 412164 388131 4 752 1873 (703877/5000:ℝ) (1437819/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B109.packed MomentCertificates.B109.count_checked MomentCertificates.B109.sum_checked
    · convert h109 using 1 <;> norm_num
    · norm_num
  have h111 : rootPrefix F 438244≤(367321/2500:ℝ) := by
    apply root_prefix_count_step F hprime 642 438244 412165 4 815 2020 (1437819/10000:ℝ) (367321/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B110.packed MomentCertificates.B110.count_checked MomentCertificates.B110.sum_checked
    · convert h110 using 1 <;> norm_num
    · norm_num
  have h112 : rootPrefix F 465124≤(750103/5000:ℝ) := by
    apply root_prefix_count_step F hprime 662 465124 438245 4 840 2047 (367321/2500:ℝ) (750103/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B111.packed MomentCertificates.B111.count_checked MomentCertificates.B111.sum_checked
    · convert h111 using 1 <;> norm_num
    · norm_num
  have h113 : rootPrefix F 494209≤(1532919/10000:ℝ) := by
    apply root_prefix_count_step F hprime 682 494209 465125 4 909 2231 (750103/5000:ℝ) (1532919/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B112.packed MomentCertificates.B112.count_checked MomentCertificates.B112.sum_checked
    · convert h112 using 1 <;> norm_num
    · norm_num
  have h114 : rootPrefix F 525625≤(783579/5000:ℝ) := by
    apply root_prefix_count_step F hprime 703 525625 494211 4 982 2407 (1532919/10000:ℝ) (783579/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B113.packed MomentCertificates.B113.count_checked MomentCertificates.B113.sum_checked
    · convert h113 using 1 <;> norm_num
    · norm_num
  have h115 : rootPrefix F 558009≤(160069/1000:ℝ) := by
    apply root_prefix_count_step F hprime 725 558009 525627 4 1012 2431 (783579/5000:ℝ) (160069/1000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B114.packed MomentCertificates.B114.count_checked MomentCertificates.B114.sum_checked
    · convert h114 using 1 <;> norm_num
    · norm_num
  have h116 : rootPrefix F 592900≤(327209/2000:ℝ) := by
    apply root_prefix_count_step F hprime 747 592900 558011 4 1091 2641 (160069/1000:ℝ) (327209/2000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B115.packed MomentCertificates.B115.count_checked MomentCertificates.B115.sum_checked
    · convert h115 using 1 <;> norm_num
    · norm_num
  have h117 : rootPrefix F 630436≤(1672487/10000:ℝ) := by
    apply root_prefix_count_step F hprime 770 630436 592901 4 1173 2806 (327209/2000:ℝ) (1672487/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B116.packed MomentCertificates.B116.count_checked MomentCertificates.B116.sum_checked
    · convert h116 using 1 <;> norm_num
    · norm_num
  have h118 : rootPrefix F 669124≤(854361/5000:ℝ) := by
    apply root_prefix_count_step F hprime 794 669124 630437 4 1209 2877 (1672487/10000:ℝ) (854361/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B117.packed MomentCertificates.B117.count_checked MomentCertificates.B117.sum_checked
    · convert h117 using 1 <;> norm_num
    · norm_num
  have h119 : rootPrefix F 710649≤(1746767/10000:ℝ) := by
    apply root_prefix_count_step F hprime 818 710649 669125 4 1298 3112 (854361/5000:ℝ) (1746767/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B118.packed MomentCertificates.B118.count_checked MomentCertificates.B118.sum_checked
    · convert h118 using 1 <;> norm_num
    · norm_num
  have h120 : rootPrefix F 755161≤(1785593/10000:ℝ) := by
    apply root_prefix_count_step F hprime 843 755161 710651 4 1391 3273 (1746767/10000:ℝ) (1785593/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B119.packed MomentCertificates.B119.count_checked MomentCertificates.B119.sum_checked
    · convert h119 using 1 <;> norm_num
    · norm_num
  have h121 : rootPrefix F 802816≤(114142/625:ℝ) := by
    apply root_prefix_count_step F hprime 869 802816 755163 4 1490 3535 (1785593/10000:ℝ) (114142/625:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B120.packed MomentCertificates.B120.count_checked MomentCertificates.B120.sum_checked
    · convert h120 using 1 <;> norm_num
    · norm_num
  have h122 : rootPrefix F 851929≤(46661/250:ℝ) := by
    apply root_prefix_count_step F hprime 896 851929 802817 4 1535 3599 (114142/625:ℝ) (46661/250:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B121.packed MomentCertificates.B121.count_checked MomentCertificates.B121.sum_checked
    · convert h121 using 1 <;> norm_num
    · norm_num
  have h123 : rootPrefix F 904401≤(1907849/10000:ℝ) := by
    apply root_prefix_count_step F hprime 923 904401 851931 4 1640 3822 (46661/250:ℝ) (1907849/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B122.packed MomentCertificates.B122.count_checked MomentCertificates.B122.sum_checked
    · convert h122 using 1 <;> norm_num
    · norm_num
  have h124 : rootPrefix F 960400≤(1950583/10000:ℝ) := by
    apply root_prefix_count_step F hprime 951 960400 904403 4 1750 4064 (1907849/10000:ℝ) (1950583/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B123.packed MomentCertificates.B123.count_checked MomentCertificates.B123.sum_checked
    · convert h123 using 1 <;> norm_num
    · norm_num
  have h125 : rootPrefix F 1020100≤(498707/2500:ℝ) := by
    apply root_prefix_count_step F hprime 980 1020100 960401 4 1866 4336 (1950583/10000:ℝ) (498707/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B124.packed MomentCertificates.B124.count_checked MomentCertificates.B124.sum_checked
    · convert h124 using 1 <;> norm_num
    · norm_num
  have h126 : rootPrefix F 1083681≤(2039967/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1010 1083681 1020101 4 1987 4559 (498707/2500:ℝ) (2039967/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B125.packed MomentCertificates.B125.count_checked MomentCertificates.B125.sum_checked
    · convert h125 using 1 <;> norm_num
    · norm_num
  have h127 : rootPrefix F 1151329≤(2086701/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1041 1151329 1083683 4 2114 4865 (2039967/10000:ℝ) (2086701/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B126.packed MomentCertificates.B126.count_checked MomentCertificates.B126.sum_checked
    · convert h126 using 1 <;> norm_num
    · norm_num
  have h128 : rootPrefix F 1223236≤(533721/2500:ℝ) := by
    apply root_prefix_count_step F hprime 1073 1223236 1151331 4 2248 5170 (2086701/10000:ℝ) (533721/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B127.packed MomentCertificates.B127.count_checked MomentCertificates.B127.sum_checked
    · convert h127 using 1 <;> norm_num
    · norm_num
  have h129 : rootPrefix F 1299600≤(218389/1000:ℝ) := by
    apply root_prefix_count_step F hprime 1106 1299600 1223237 4 2387 5420 (533721/2500:ℝ) (218389/1000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B128.packed MomentCertificates.B128.count_checked MomentCertificates.B128.sum_checked
    · convert h128 using 1 <;> norm_num
    · norm_num
  have h130 : rootPrefix F 1380625≤(558569/2500:ℝ) := by
    apply root_prefix_count_step F hprime 1140 1380625 1299601 4 2533 5744 (218389/1000:ℝ) (558569/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B129.packed MomentCertificates.B129.count_checked MomentCertificates.B129.sum_checked
    · convert h129 using 1 <;> norm_num
    · norm_num
  have h131 : rootPrefix F 1466521≤(571501/2500:ℝ) := by
    apply root_prefix_count_step F hprime 1175 1466521 1380627 4 2685 6078 (558569/2500:ℝ) (571501/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B130.packed MomentCertificates.B130.count_checked MomentCertificates.B130.sum_checked
    · convert h130 using 1 <;> norm_num
    · norm_num
  have h132 : rootPrefix F 1557504≤(2338763/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1211 1557504 1466523 4 2844 6389 (571501/2500:ℝ) (2338763/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B131.packed MomentCertificates.B131.count_checked MomentCertificates.B131.sum_checked
    · convert h131 using 1 <;> norm_num
    · norm_num
  have h133 : rootPrefix F 1653796≤(1196261/5000:ℝ) := by
    apply root_prefix_count_step F hprime 1248 1653796 1557505 4 3010 6709 (2338763/10000:ℝ) (1196261/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B132.packed MomentCertificates.B132.count_checked MomentCertificates.B132.sum_checked
    · convert h132 using 1 <;> norm_num
    · norm_num
  have h134 : rootPrefix F 1755625≤(611933/2500:ℝ) := by
    apply root_prefix_count_step F hprime 1286 1755625 1653797 4 3183 7100 (1196261/5000:ℝ) (611933/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B133.packed MomentCertificates.B133.count_checked MomentCertificates.B133.sum_checked
    · convert h133 using 1 <;> norm_num
    · norm_num
  have h135 : rootPrefix F 1863225≤(313009/1250:ℝ) := by
    apply root_prefix_count_step F hprime 1325 1863225 1755627 4 3363 7465 (611933/2500:ℝ) (313009/1250:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B134.packed MomentCertificates.B134.count_checked MomentCertificates.B134.sum_checked
    · convert h134 using 1 <;> norm_num
    · norm_num
  have h136 : rootPrefix F 1976836≤(160097/625:ℝ) := by
    apply root_prefix_count_step F hprime 1365 1976836 1863227 4 3551 7846 (313009/1250:ℝ) (160097/625:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B135.packed MomentCertificates.B135.count_checked MomentCertificates.B135.sum_checked
    · convert h135 using 1 <;> norm_num
    · norm_num
  have h137 : rootPrefix F 2099601≤(131089/500:ℝ) := by
    apply root_prefix_count_step F hprime 1406 2099601 1976837 4 3837 8468 (160097/625:ℝ) (131089/500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B136.packed MomentCertificates.B136.count_checked MomentCertificates.B136.sum_checked
    · convert h136 using 1 <;> norm_num
    · norm_num
  have h138 : rootPrefix F 2229049≤(268303/1000:ℝ) := by
    apply root_prefix_count_step F hprime 1449 2229049 2099603 4 4046 8875 (131089/500:ℝ) (268303/1000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B137.packed MomentCertificates.B137.count_checked MomentCertificates.B137.sum_checked
    · convert h137 using 1 <;> norm_num
    · norm_num
  have h139 : rootPrefix F 2365444≤(686317/2500:ℝ) := by
    apply root_prefix_count_step F hprime 1493 2365444 2229051 4 4263 9292 (268303/1000:ℝ) (686317/2500:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B138.packed MomentCertificates.B138.count_checked MomentCertificates.B138.sum_checked
    · convert h138 using 1 <;> norm_num
    · norm_num
  have h140 : rootPrefix F 2512225≤(1405017/5000:ℝ) := by
    apply root_prefix_count_step F hprime 1538 2512225 2365445 4 4587 9961 (686317/2500:ℝ) (1405017/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B139.packed MomentCertificates.B139.count_checked MomentCertificates.B139.sum_checked
    · convert h139 using 1 <;> norm_num
    · norm_num
  have h141 : rootPrefix F 2666689≤(1438131/5000:ℝ) := by
    apply root_prefix_count_step F hprime 1585 2666689 2512227 4 4827 10497 (1405017/5000:ℝ) (1438131/5000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B140.packed MomentCertificates.B140.count_checked MomentCertificates.B140.sum_checked
    · convert h140 using 1 <;> norm_num
    · norm_num
  have h142 : rootPrefix F 2829124≤(2943323/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1633 2829124 2666691 4 5077 10951 (1438131/5000:ℝ) (2943323/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B141.packed MomentCertificates.B141.count_checked MomentCertificates.B141.sum_checked
    · convert h141 using 1 <;> norm_num
    · norm_num
  have h143 : rootPrefix F 3003289≤(376603/1250:ℝ) := by
    apply root_prefix_count_step F hprime 1682 3003289 2829125 4 5443 11690 (2943323/10000:ℝ) (376603/1250:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B142.packed MomentCertificates.B142.count_checked MomentCertificates.B142.sum_checked
    · convert h142 using 1 <;> norm_num
    · norm_num
  have h144 : rootPrefix F 3186225≤(3083413/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1733 3186225 3003291 4 5717 12233 (376603/1250:ℝ) (3083413/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B143.packed MomentCertificates.B143.count_checked MomentCertificates.B143.sum_checked
    · convert h143 using 1 <;> norm_num
    · norm_num
  have h145 : rootPrefix F 3381921≤(3156579/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1785 3381921 3186227 4 6116 13060 (3083413/10000:ℝ) (3156579/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B144.packed MomentCertificates.B144.count_checked MomentCertificates.B144.sum_checked
    · convert h144 using 1 <;> norm_num
    · norm_num
  have h146 : rootPrefix F 3591025≤(3231637/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1839 3591025 3381923 4 6535 13803 (3156579/10000:ℝ) (3231637/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B145.packed MomentCertificates.B145.count_checked MomentCertificates.B145.sum_checked
    · convert h145 using 1 <;> norm_num
    · norm_num
  have h147 : rootPrefix F 3810304≤(3308339/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1895 3810304 3591027 4 6853 14535 (3231637/10000:ℝ) (3308339/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B146.packed MomentCertificates.B146.count_checked MomentCertificates.B146.sum_checked
    · convert h146 using 1 <;> norm_num
    · norm_num
  have h148 : rootPrefix F 4000000≤(3372269/10000:ℝ) := by
    apply root_prefix_count_step F hprime 1952 4000000 3810305 4 5928 12479 (3308339/10000:ℝ) (3372269/10000:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [PsiFinite.baseCover]) MomentCertificates.B147.packed MomentCertificates.B147.count_checked MomentCertificates.B147.sum_checked
    · convert h147 using 1 <;> norm_num
    · norm_num
  have hf : F.filter (fun p=>p≤4000000)=F := filter_eq_self.mpr (fun p hp => (hF p hp).2)
  simp only [rootPrefix,hf] at h148
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
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 340 := by
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
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*v d) ≤ exp 350 := by
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
    (∑ d ∈ Q.divisors, 1/sqrt (d:ℝ)) ≤ exp 340 ∧
    (∑ d ∈ Q.divisors, sqrt (d:ℝ)*AnalyticNumberTheory.Sieve.goldbachNu d) ≤ exp 350 := by
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
end ChenEffective.GRHSub12
end
