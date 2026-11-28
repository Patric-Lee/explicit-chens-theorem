import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C320
import GRHQuarterCertificates.C321
import GRHQuarterCertificates.C322
import GRHQuarterCertificates.C323
import GRHQuarterCertificates.C324
import GRHQuarterCertificates.C325
import GRHQuarterCertificates.C326
import GRHQuarterCertificates.C327
import GRHQuarterCertificates.C328
import GRHQuarterCertificates.C329
import GRHQuarterCertificates.C330
import GRHQuarterCertificates.C331
import GRHQuarterCertificates.C332
import GRHQuarterCertificates.C333
import GRHQuarterCertificates.C334
import GRHQuarterCertificates.C335
import GRHQuarterCertificates.C336
import GRHQuarterCertificates.C337
import GRHQuarterCertificates.C338
import GRHQuarterCertificates.C339
import GRHQuarterCertificates.C340
import GRHQuarterCertificates.C341
import GRHQuarterCertificates.C342
import GRHQuarterCertificates.C343
import GRHQuarterCertificates.C344
import GRHQuarterCertificates.C345
import GRHQuarterCertificates.C346
import GRHQuarterCertificates.C347
import GRHQuarterCertificates.C348
import GRHQuarterCertificates.C349
import GRHQuarterCertificates.C350
import GRHQuarterCertificates.C351
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup10_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 2729744 ≤ envelopePrefix F 2467600+(277359837529:ℝ)/denominator := by
  have h0 : envelopePrefix F 2475792 ≤ envelopePrefix F 2467600+(8749258951:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2467601) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C320.data C320.counts_checked C320.bounds_checked C320.weighted_checked
  have h1 : envelopePrefix F 2483984 ≤ envelopePrefix F 2475792+(8873107234:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2475793) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C321.data C321.counts_checked C321.bounds_checked C321.weighted_checked
  have h2 : envelopePrefix F 2492176 ≤ envelopePrefix F 2483984+(9141456124:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2483985) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C322.data C322.counts_checked C322.bounds_checked C322.weighted_checked
  have h3 : envelopePrefix F 2500368 ≤ envelopePrefix F 2492176+(8909511452:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2492177) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C323.data C323.counts_checked C323.bounds_checked C323.weighted_checked
  have h4 : envelopePrefix F 2508560 ≤ envelopePrefix F 2500368+(8984070656:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2500369) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C324.data C324.counts_checked C324.bounds_checked C324.weighted_checked
  have h5 : envelopePrefix F 2516752 ≤ envelopePrefix F 2508560+(8834161987:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2508561) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C325.data C325.counts_checked C325.bounds_checked C325.weighted_checked
  have h6 : envelopePrefix F 2524944 ≤ envelopePrefix F 2516752+(9099419310:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2516753) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C326.data C326.counts_checked C326.bounds_checked C326.weighted_checked
  have h7 : envelopePrefix F 2533136 ≤ envelopePrefix F 2524944+(8950279401:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2524945) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C327.data C327.counts_checked C327.bounds_checked C327.weighted_checked
  have h8 : envelopePrefix F 2541328 ≤ envelopePrefix F 2533136+(8563245133:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2533137) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C328.data C328.counts_checked C328.bounds_checked C328.weighted_checked
  have h9 : envelopePrefix F 2549520 ≤ envelopePrefix F 2541328+(8748501895:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2541329) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C329.data C329.counts_checked C329.bounds_checked C329.weighted_checked
  have h10 : envelopePrefix F 2557712 ≤ envelopePrefix F 2549520+(8664329465:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2549521) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C330.data C330.counts_checked C330.bounds_checked C330.weighted_checked
  have h11 : envelopePrefix F 2565904 ≤ envelopePrefix F 2557712+(8691118473:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2557713) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C331.data C331.counts_checked C331.bounds_checked C331.weighted_checked
  have h12 : envelopePrefix F 2574096 ≤ envelopePrefix F 2565904+(8859071195:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2565905) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C332.data C332.counts_checked C332.bounds_checked C332.weighted_checked
  have h13 : envelopePrefix F 2582288 ≤ envelopePrefix F 2574096+(9245898605:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2574097) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C333.data C333.counts_checked C333.bounds_checked C333.weighted_checked
  have h14 : envelopePrefix F 2590480 ≤ envelopePrefix F 2582288+(8722726711:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2582289) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C334.data C334.counts_checked C334.bounds_checked C334.weighted_checked
  have h15 : envelopePrefix F 2598672 ≤ envelopePrefix F 2590480+(8561391122:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2590481) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C335.data C335.counts_checked C335.bounds_checked C335.weighted_checked
  have h16 : envelopePrefix F 2606864 ≤ envelopePrefix F 2598672+(8385572741:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2598673) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C336.data C336.counts_checked C336.bounds_checked C336.weighted_checked
  have h17 : envelopePrefix F 2615056 ≤ envelopePrefix F 2606864+(8645508049:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2606865) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C337.data C337.counts_checked C337.bounds_checked C337.weighted_checked
  have h18 : envelopePrefix F 2623248 ≤ envelopePrefix F 2615056+(8547968576:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2615057) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C338.data C338.counts_checked C338.bounds_checked C338.weighted_checked
  have h19 : envelopePrefix F 2631440 ≤ envelopePrefix F 2623248+(8635991107:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2623249) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C339.data C339.counts_checked C339.bounds_checked C339.weighted_checked
  have h20 : envelopePrefix F 2639632 ≤ envelopePrefix F 2631440+(8477306218:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2631441) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C340.data C340.counts_checked C340.bounds_checked C340.weighted_checked
  have h21 : envelopePrefix F 2647824 ≤ envelopePrefix F 2639632+(8796189538:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2639633) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C341.data C341.counts_checked C341.bounds_checked C341.weighted_checked
  have h22 : envelopePrefix F 2656016 ≤ envelopePrefix F 2647824+(8622042604:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2647825) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C342.data C342.counts_checked C342.bounds_checked C342.weighted_checked
  have h23 : envelopePrefix F 2664208 ≤ envelopePrefix F 2656016+(8541016213:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2656017) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C343.data C343.counts_checked C343.bounds_checked C343.weighted_checked
  have h24 : envelopePrefix F 2672400 ≤ envelopePrefix F 2664208+(8200118562:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2664209) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C344.data C344.counts_checked C344.bounds_checked C344.weighted_checked
  have h25 : envelopePrefix F 2680592 ≤ envelopePrefix F 2672400+(8425234796:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2672401) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C345.data C345.counts_checked C345.bounds_checked C345.weighted_checked
  have h26 : envelopePrefix F 2688784 ≤ envelopePrefix F 2680592+(8421279455:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2680593) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C346.data C346.counts_checked C346.bounds_checked C346.weighted_checked
  have h27 : envelopePrefix F 2696976 ≤ envelopePrefix F 2688784+(8599701920:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2688785) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C347.data C347.counts_checked C347.bounds_checked C347.weighted_checked
  have h28 : envelopePrefix F 2705168 ≤ envelopePrefix F 2696976+(8534436478:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2696977) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C348.data C348.counts_checked C348.bounds_checked C348.weighted_checked
  have h29 : envelopePrefix F 2713360 ≤ envelopePrefix F 2705168+(8409179401:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2705169) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C349.data C349.counts_checked C349.bounds_checked C349.weighted_checked
  have h30 : envelopePrefix F 2721552 ≤ envelopePrefix F 2713360+(8480818121:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2713361) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C350.data C350.counts_checked C350.bounds_checked C350.weighted_checked
  have h31 : envelopePrefix F 2729744 ≤ envelopePrefix F 2721552+(8039926036:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2721553) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C351.data C351.counts_checked C351.bounds_checked C351.weighted_checked
  have m0 : envelopePrefix F 2483984 ≤ envelopePrefix F 2467600+(17622366185:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 2500368 ≤ envelopePrefix F 2483984+(18050967576:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 2516752 ≤ envelopePrefix F 2500368+(17818232643:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 2533136 ≤ envelopePrefix F 2516752+(18049698711:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 2549520 ≤ envelopePrefix F 2533136+(17311747028:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 2565904 ≤ envelopePrefix F 2549520+(17355447938:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 2582288 ≤ envelopePrefix F 2565904+(18104969800:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 2598672 ≤ envelopePrefix F 2582288+(17284117833:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 2615056 ≤ envelopePrefix F 2598672+(17031080790:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 2631440 ≤ envelopePrefix F 2615056+(17183959683:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 2647824 ≤ envelopePrefix F 2631440+(17273495756:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 2664208 ≤ envelopePrefix F 2647824+(17163058817:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 2680592 ≤ envelopePrefix F 2664208+(16625353358:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 2696976 ≤ envelopePrefix F 2680592+(17020981375:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 2713360 ≤ envelopePrefix F 2696976+(16943615879:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 2729744 ≤ envelopePrefix F 2713360+(16520744157:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 2500368 ≤ envelopePrefix F 2467600+(35673333761:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 2533136 ≤ envelopePrefix F 2500368+(35867931354:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 2565904 ≤ envelopePrefix F 2533136+(34667194966:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 2598672 ≤ envelopePrefix F 2565904+(35389087633:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 2631440 ≤ envelopePrefix F 2598672+(34215040473:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 2664208 ≤ envelopePrefix F 2631440+(34436554573:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 2696976 ≤ envelopePrefix F 2664208+(33646334733:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 2729744 ≤ envelopePrefix F 2696976+(33464360036:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 2533136 ≤ envelopePrefix F 2467600+(71541265115:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 2598672 ≤ envelopePrefix F 2533136+(70056282599:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 2664208 ≤ envelopePrefix F 2598672+(68651595046:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 2729744 ≤ envelopePrefix F 2664208+(67110694769:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 2598672 ≤ envelopePrefix F 2467600+(141597547714:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 2729744 ≤ envelopePrefix F 2598672+(135762289815:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 2729744 ≤ envelopePrefix F 2467600+(277359837529:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup10_bound
end ChenEffective.H10Band
end
