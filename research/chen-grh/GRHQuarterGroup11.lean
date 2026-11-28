import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C352
import GRHQuarterCertificates.C353
import GRHQuarterCertificates.C354
import GRHQuarterCertificates.C355
import GRHQuarterCertificates.C356
import GRHQuarterCertificates.C357
import GRHQuarterCertificates.C358
import GRHQuarterCertificates.C359
import GRHQuarterCertificates.C360
import GRHQuarterCertificates.C361
import GRHQuarterCertificates.C362
import GRHQuarterCertificates.C363
import GRHQuarterCertificates.C364
import GRHQuarterCertificates.C365
import GRHQuarterCertificates.C366
import GRHQuarterCertificates.C367
import GRHQuarterCertificates.C368
import GRHQuarterCertificates.C369
import GRHQuarterCertificates.C370
import GRHQuarterCertificates.C371
import GRHQuarterCertificates.C372
import GRHQuarterCertificates.C373
import GRHQuarterCertificates.C374
import GRHQuarterCertificates.C375
import GRHQuarterCertificates.C376
import GRHQuarterCertificates.C377
import GRHQuarterCertificates.C378
import GRHQuarterCertificates.C379
import GRHQuarterCertificates.C380
import GRHQuarterCertificates.C381
import GRHQuarterCertificates.C382
import GRHQuarterCertificates.C383
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup11_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 2991888 ≤ envelopePrefix F 2729744+(255822042316:ℝ)/denominator := by
  have h0 : envelopePrefix F 2737936 ≤ envelopePrefix F 2729744+(7856948344:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2729745) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C352.data C352.counts_checked C352.bounds_checked C352.weighted_checked
  have h1 : envelopePrefix F 2746128 ≤ envelopePrefix F 2737936+(8483904547:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2737937) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C353.data C353.counts_checked C353.bounds_checked C353.weighted_checked
  have h2 : envelopePrefix F 2754320 ≤ envelopePrefix F 2746128+(8120828059:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2746129) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C354.data C354.counts_checked C354.bounds_checked C354.weighted_checked
  have h3 : envelopePrefix F 2762512 ≤ envelopePrefix F 2754320+(8415776831:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2754321) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C355.data C355.counts_checked C355.bounds_checked C355.weighted_checked
  have h4 : envelopePrefix F 2770704 ≤ envelopePrefix F 2762512+(8084744637:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2762513) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C356.data C356.counts_checked C356.bounds_checked C356.weighted_checked
  have h5 : envelopePrefix F 2778896 ≤ envelopePrefix F 2770704+(8230290159:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2770705) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C357.data C357.counts_checked C357.bounds_checked C357.weighted_checked
  have h6 : envelopePrefix F 2787088 ≤ envelopePrefix F 2778896+(8226681380:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2778897) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C358.data C358.counts_checked C358.bounds_checked C358.weighted_checked
  have h7 : envelopePrefix F 2795280 ≤ envelopePrefix F 2787088+(7942330551:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2787089) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C359.data C359.counts_checked C359.bounds_checked C359.weighted_checked
  have h8 : envelopePrefix F 2803472 ≤ envelopePrefix F 2795280+(8279074941:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2795281) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C360.data C360.counts_checked C360.bounds_checked C360.weighted_checked
  have h9 : envelopePrefix F 2811664 ≤ envelopePrefix F 2803472+(8584887151:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2803473) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C361.data C361.counts_checked C361.bounds_checked C361.weighted_checked
  have h10 : envelopePrefix F 2819856 ≤ envelopePrefix F 2811664+(8228268870:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2811665) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C362.data C362.counts_checked C362.bounds_checked C362.weighted_checked
  have h11 : envelopePrefix F 2828048 ≤ envelopePrefix F 2819856+(7888251698:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2819857) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C363.data C363.counts_checked C363.bounds_checked C363.weighted_checked
  have h12 : envelopePrefix F 2836240 ≤ envelopePrefix F 2828048+(8412103375:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2828049) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C364.data C364.counts_checked C364.bounds_checked C364.weighted_checked
  have h13 : envelopePrefix F 2844432 ≤ envelopePrefix F 2836240+(8291770802:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2836241) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C365.data C365.counts_checked C365.bounds_checked C365.weighted_checked
  have h14 : envelopePrefix F 2852624 ≤ envelopePrefix F 2844432+(7880318958:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2844433) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C366.data C366.counts_checked C366.bounds_checked C366.weighted_checked
  have h15 : envelopePrefix F 2860816 ≤ envelopePrefix F 2852624+(7863569751:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2852625) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C367.data C367.counts_checked C367.bounds_checked C367.weighted_checked
  have h16 : envelopePrefix F 2869008 ≤ envelopePrefix F 2860816+(8078695000:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2860817) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C368.data C368.counts_checked C368.bounds_checked C368.weighted_checked
  have h17 : envelopePrefix F 2877200 ≤ envelopePrefix F 2869008+(7699547798:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2869009) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C369.data C369.counts_checked C369.bounds_checked C369.weighted_checked
  have h18 : envelopePrefix F 2885392 ≤ envelopePrefix F 2877200+(7928550848:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2877201) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C370.data C370.counts_checked C370.bounds_checked C370.weighted_checked
  have h19 : envelopePrefix F 2893584 ≤ envelopePrefix F 2885392+(7868587497:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2885393) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C371.data C371.counts_checked C371.bounds_checked C371.weighted_checked
  have h20 : envelopePrefix F 2901776 ≤ envelopePrefix F 2893584+(7880490170:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2893585) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C372.data C372.counts_checked C372.bounds_checked C372.weighted_checked
  have h21 : envelopePrefix F 2909968 ≤ envelopePrefix F 2901776+(7935632287:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2901777) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C373.data C373.counts_checked C373.bounds_checked C373.weighted_checked
  have h22 : envelopePrefix F 2918160 ≤ envelopePrefix F 2909968+(7632628180:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2909969) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C374.data C374.counts_checked C374.bounds_checked C374.weighted_checked
  have h23 : envelopePrefix F 2926352 ≤ envelopePrefix F 2918160+(8173982201:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2918161) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C375.data C375.counts_checked C375.bounds_checked C375.weighted_checked
  have h24 : envelopePrefix F 2934544 ≤ envelopePrefix F 2926352+(7500738081:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2926353) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C376.data C376.counts_checked C376.bounds_checked C376.weighted_checked
  have h25 : envelopePrefix F 2942736 ≤ envelopePrefix F 2934544+(7883831493:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2934545) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C377.data C377.counts_checked C377.bounds_checked C377.weighted_checked
  have h26 : envelopePrefix F 2950928 ≤ envelopePrefix F 2942736+(7710778319:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2942737) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C378.data C378.counts_checked C378.bounds_checked C378.weighted_checked
  have h27 : envelopePrefix F 2959120 ≤ envelopePrefix F 2950928+(7539170240:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2950929) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C379.data C379.counts_checked C379.bounds_checked C379.weighted_checked
  have h28 : envelopePrefix F 2967312 ≤ envelopePrefix F 2959120+(7990067633:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2959121) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C380.data C380.counts_checked C380.bounds_checked C380.weighted_checked
  have h29 : envelopePrefix F 2975504 ≤ envelopePrefix F 2967312+(7804175132:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2967313) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C381.data C381.counts_checked C381.bounds_checked C381.weighted_checked
  have h30 : envelopePrefix F 2983696 ≤ envelopePrefix F 2975504+(7844150739:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2975505) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C382.data C382.counts_checked C382.bounds_checked C382.weighted_checked
  have h31 : envelopePrefix F 2991888 ≤ envelopePrefix F 2983696+(7561266644:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2983697) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C383.data C383.counts_checked C383.bounds_checked C383.weighted_checked
  have m0 : envelopePrefix F 2746128 ≤ envelopePrefix F 2729744+(16340852891:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 2762512 ≤ envelopePrefix F 2746128+(16536604890:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 2778896 ≤ envelopePrefix F 2762512+(16315034796:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 2795280 ≤ envelopePrefix F 2778896+(16169011931:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 2811664 ≤ envelopePrefix F 2795280+(16863962092:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 2828048 ≤ envelopePrefix F 2811664+(16116520568:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 2844432 ≤ envelopePrefix F 2828048+(16703874177:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 2860816 ≤ envelopePrefix F 2844432+(15743888709:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 2877200 ≤ envelopePrefix F 2860816+(15778242798:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 2893584 ≤ envelopePrefix F 2877200+(15797138345:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 2909968 ≤ envelopePrefix F 2893584+(15816122457:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 2926352 ≤ envelopePrefix F 2909968+(15806610381:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 2942736 ≤ envelopePrefix F 2926352+(15384569574:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 2959120 ≤ envelopePrefix F 2942736+(15249948559:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 2975504 ≤ envelopePrefix F 2959120+(15794242765:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 2991888 ≤ envelopePrefix F 2975504+(15405417383:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 2762512 ≤ envelopePrefix F 2729744+(32877457781:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 2795280 ≤ envelopePrefix F 2762512+(32484046727:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 2828048 ≤ envelopePrefix F 2795280+(32980482660:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 2860816 ≤ envelopePrefix F 2828048+(32447762886:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 2893584 ≤ envelopePrefix F 2860816+(31575381143:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 2926352 ≤ envelopePrefix F 2893584+(31622732838:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 2959120 ≤ envelopePrefix F 2926352+(30634518133:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 2991888 ≤ envelopePrefix F 2959120+(31199660148:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 2795280 ≤ envelopePrefix F 2729744+(65361504508:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 2860816 ≤ envelopePrefix F 2795280+(65428245546:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 2926352 ≤ envelopePrefix F 2860816+(63198113981:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 2991888 ≤ envelopePrefix F 2926352+(61834178281:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 2860816 ≤ envelopePrefix F 2729744+(130789750054:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 2991888 ≤ envelopePrefix F 2860816+(125032292262:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 2991888 ≤ envelopePrefix F 2729744+(255822042316:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup11_bound
end ChenEffective.H10Band
end
