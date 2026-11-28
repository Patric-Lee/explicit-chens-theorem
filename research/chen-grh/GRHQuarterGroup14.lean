import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C448
import GRHQuarterCertificates.C449
import GRHQuarterCertificates.C450
import GRHQuarterCertificates.C451
import GRHQuarterCertificates.C452
import GRHQuarterCertificates.C453
import GRHQuarterCertificates.C454
import GRHQuarterCertificates.C455
import GRHQuarterCertificates.C456
import GRHQuarterCertificates.C457
import GRHQuarterCertificates.C458
import GRHQuarterCertificates.C459
import GRHQuarterCertificates.C460
import GRHQuarterCertificates.C461
import GRHQuarterCertificates.C462
import GRHQuarterCertificates.C463
import GRHQuarterCertificates.C464
import GRHQuarterCertificates.C465
import GRHQuarterCertificates.C466
import GRHQuarterCertificates.C467
import GRHQuarterCertificates.C468
import GRHQuarterCertificates.C469
import GRHQuarterCertificates.C470
import GRHQuarterCertificates.C471
import GRHQuarterCertificates.C472
import GRHQuarterCertificates.C473
import GRHQuarterCertificates.C474
import GRHQuarterCertificates.C475
import GRHQuarterCertificates.C476
import GRHQuarterCertificates.C477
import GRHQuarterCertificates.C478
import GRHQuarterCertificates.C479
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup14_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 3778320 ≤ envelopePrefix F 3516176+(209934061144:ℝ)/denominator := by
  have h0 : envelopePrefix F 3524368 ≤ envelopePrefix F 3516176+(6462339745:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3516177) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C448.data C448.counts_checked C448.bounds_checked C448.weighted_checked
  have h1 : envelopePrefix F 3532560 ≤ envelopePrefix F 3524368+(6587469568:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3524369) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C449.data C449.counts_checked C449.bounds_checked C449.weighted_checked
  have h2 : envelopePrefix F 3540752 ≤ envelopePrefix F 3532560+(6650535300:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3532561) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C450.data C450.counts_checked C450.bounds_checked C450.weighted_checked
  have h3 : envelopePrefix F 3548944 ≤ envelopePrefix F 3540752+(6675896940:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3540753) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C451.data C451.counts_checked C451.bounds_checked C451.weighted_checked
  have h4 : envelopePrefix F 3557136 ≤ envelopePrefix F 3548944+(6651965969:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3548945) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C452.data C452.counts_checked C452.bounds_checked C452.weighted_checked
  have h5 : envelopePrefix F 3565328 ≤ envelopePrefix F 3557136+(6726804970:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3557137) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C453.data C453.counts_checked C453.bounds_checked C453.weighted_checked
  have h6 : envelopePrefix F 3573520 ≤ envelopePrefix F 3565328+(6678483676:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3565329) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C454.data C454.counts_checked C454.bounds_checked C454.weighted_checked
  have h7 : envelopePrefix F 3581712 ≤ envelopePrefix F 3573520+(6495028617:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3573521) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C455.data C455.counts_checked C455.bounds_checked C455.weighted_checked
  have h8 : envelopePrefix F 3589904 ≤ envelopePrefix F 3581712+(6729095901:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3581713) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C456.data C456.counts_checked C456.bounds_checked C456.weighted_checked
  have h9 : envelopePrefix F 3598096 ≤ envelopePrefix F 3589904+(6729614812:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3589905) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C457.data C457.counts_checked C457.bounds_checked C457.weighted_checked
  have h10 : envelopePrefix F 3606288 ≤ envelopePrefix F 3598096+(6681608386:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3598097) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C458.data C458.counts_checked C458.bounds_checked C458.weighted_checked
  have h11 : envelopePrefix F 3614480 ≤ envelopePrefix F 3606288+(7048289564:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3606289) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C459.data C459.counts_checked C459.bounds_checked C459.weighted_checked
  have h12 : envelopePrefix F 3622672 ≤ envelopePrefix F 3614480+(6695322979:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3614481) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C460.data C460.counts_checked C460.bounds_checked C460.weighted_checked
  have h13 : envelopePrefix F 3630864 ≤ envelopePrefix F 3622672+(6708444562:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3622673) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C461.data C461.counts_checked C461.bounds_checked C461.weighted_checked
  have h14 : envelopePrefix F 3639056 ≤ envelopePrefix F 3630864+(6418098734:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3630865) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C462.data C462.counts_checked C462.bounds_checked C462.weighted_checked
  have h15 : envelopePrefix F 3647248 ≤ envelopePrefix F 3639056+(6492042801:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3639057) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C463.data C463.counts_checked C463.bounds_checked C463.weighted_checked
  have h16 : envelopePrefix F 3655440 ≤ envelopePrefix F 3647248+(6118267735:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3647249) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C464.data C464.counts_checked C464.bounds_checked C464.weighted_checked
  have h17 : envelopePrefix F 3663632 ≤ envelopePrefix F 3655440+(6687527385:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3655441) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C465.data C465.counts_checked C465.bounds_checked C465.weighted_checked
  have h18 : envelopePrefix F 3671824 ≤ envelopePrefix F 3663632+(6483434029:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3663633) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C466.data C466.counts_checked C466.bounds_checked C466.weighted_checked
  have h19 : envelopePrefix F 3680016 ≤ envelopePrefix F 3671824+(7050010475:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3671825) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C467.data C467.counts_checked C467.bounds_checked C467.weighted_checked
  have h20 : envelopePrefix F 3688208 ≤ envelopePrefix F 3680016+(6245470890:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3680017) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C468.data C468.counts_checked C468.bounds_checked C468.weighted_checked
  have h21 : envelopePrefix F 3696400 ≤ envelopePrefix F 3688208+(6678784605:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3688209) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C469.data C469.counts_checked C469.bounds_checked C469.weighted_checked
  have h22 : envelopePrefix F 3704592 ≤ envelopePrefix F 3696400+(6548069418:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3696401) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C470.data C470.counts_checked C470.bounds_checked C470.weighted_checked
  have h23 : envelopePrefix F 3712784 ≤ envelopePrefix F 3704592+(6393707834:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3704593) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C471.data C471.counts_checked C471.bounds_checked C471.weighted_checked
  have h24 : envelopePrefix F 3720976 ≤ envelopePrefix F 3712784+(6538261693:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3712785) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C472.data C472.counts_checked C472.bounds_checked C472.weighted_checked
  have h25 : envelopePrefix F 3729168 ≤ envelopePrefix F 3720976+(6658506404:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3720977) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C473.data C473.counts_checked C473.bounds_checked C473.weighted_checked
  have h26 : envelopePrefix F 3737360 ≤ envelopePrefix F 3729168+(6623878152:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3729169) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C474.data C474.counts_checked C474.bounds_checked C474.weighted_checked
  have h27 : envelopePrefix F 3745552 ≤ envelopePrefix F 3737360+(6126158077:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3737361) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C475.data C475.counts_checked C475.bounds_checked C475.weighted_checked
  have h28 : envelopePrefix F 3753744 ≤ envelopePrefix F 3745552+(6613898563:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3745553) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C476.data C476.counts_checked C476.bounds_checked C476.weighted_checked
  have h29 : envelopePrefix F 3761936 ≤ envelopePrefix F 3753744+(6106310373:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3753745) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C477.data C477.counts_checked C477.bounds_checked C477.weighted_checked
  have h30 : envelopePrefix F 3770128 ≤ envelopePrefix F 3761936+(6332352195:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3761937) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C478.data C478.counts_checked C478.bounds_checked C478.weighted_checked
  have h31 : envelopePrefix F 3778320 ≤ envelopePrefix F 3770128+(6298380792:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3770129) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C479.data C479.counts_checked C479.bounds_checked C479.weighted_checked
  have m0 : envelopePrefix F 3532560 ≤ envelopePrefix F 3516176+(13049809313:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 3548944 ≤ envelopePrefix F 3532560+(13326432240:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 3565328 ≤ envelopePrefix F 3548944+(13378770939:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 3581712 ≤ envelopePrefix F 3565328+(13173512293:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 3598096 ≤ envelopePrefix F 3581712+(13458710713:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 3614480 ≤ envelopePrefix F 3598096+(13729897950:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 3630864 ≤ envelopePrefix F 3614480+(13403767541:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 3647248 ≤ envelopePrefix F 3630864+(12910141535:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 3663632 ≤ envelopePrefix F 3647248+(12805795120:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 3680016 ≤ envelopePrefix F 3663632+(13533444504:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 3696400 ≤ envelopePrefix F 3680016+(12924255495:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 3712784 ≤ envelopePrefix F 3696400+(12941777252:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 3729168 ≤ envelopePrefix F 3712784+(13196768097:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 3745552 ≤ envelopePrefix F 3729168+(12750036229:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 3761936 ≤ envelopePrefix F 3745552+(12720208936:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 3778320 ≤ envelopePrefix F 3761936+(12630732987:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 3548944 ≤ envelopePrefix F 3516176+(26376241553:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 3581712 ≤ envelopePrefix F 3548944+(26552283232:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 3614480 ≤ envelopePrefix F 3581712+(27188608663:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 3647248 ≤ envelopePrefix F 3614480+(26313909076:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 3680016 ≤ envelopePrefix F 3647248+(26339239624:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 3712784 ≤ envelopePrefix F 3680016+(25866032747:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 3745552 ≤ envelopePrefix F 3712784+(25946804326:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 3778320 ≤ envelopePrefix F 3745552+(25350941923:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 3581712 ≤ envelopePrefix F 3516176+(52928524785:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 3647248 ≤ envelopePrefix F 3581712+(53502517739:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 3712784 ≤ envelopePrefix F 3647248+(52205272371:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 3778320 ≤ envelopePrefix F 3712784+(51297746249:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 3647248 ≤ envelopePrefix F 3516176+(106431042524:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 3778320 ≤ envelopePrefix F 3647248+(103503018620:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 3778320 ≤ envelopePrefix F 3516176+(209934061144:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup14_bound
end ChenEffective.H10Band
end
