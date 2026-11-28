import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C384
import GRHQuarterCertificates.C385
import GRHQuarterCertificates.C386
import GRHQuarterCertificates.C387
import GRHQuarterCertificates.C388
import GRHQuarterCertificates.C389
import GRHQuarterCertificates.C390
import GRHQuarterCertificates.C391
import GRHQuarterCertificates.C392
import GRHQuarterCertificates.C393
import GRHQuarterCertificates.C394
import GRHQuarterCertificates.C395
import GRHQuarterCertificates.C396
import GRHQuarterCertificates.C397
import GRHQuarterCertificates.C398
import GRHQuarterCertificates.C399
import GRHQuarterCertificates.C400
import GRHQuarterCertificates.C401
import GRHQuarterCertificates.C402
import GRHQuarterCertificates.C403
import GRHQuarterCertificates.C404
import GRHQuarterCertificates.C405
import GRHQuarterCertificates.C406
import GRHQuarterCertificates.C407
import GRHQuarterCertificates.C408
import GRHQuarterCertificates.C409
import GRHQuarterCertificates.C410
import GRHQuarterCertificates.C411
import GRHQuarterCertificates.C412
import GRHQuarterCertificates.C413
import GRHQuarterCertificates.C414
import GRHQuarterCertificates.C415
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup12_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 3254032 ≤ envelopePrefix F 2991888+(239094483282:ℝ)/denominator := by
  have h0 : envelopePrefix F 3000080 ≤ envelopePrefix F 2991888+(7896269017:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2991889) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C384.data C384.counts_checked C384.bounds_checked C384.weighted_checked
  have h1 : envelopePrefix F 3008272 ≤ envelopePrefix F 3000080+(7726159846:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3000081) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C385.data C385.counts_checked C385.bounds_checked C385.weighted_checked
  have h2 : envelopePrefix F 3016464 ≤ envelopePrefix F 3008272+(7598767430:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3008273) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C386.data C386.counts_checked C386.bounds_checked C386.weighted_checked
  have h3 : envelopePrefix F 3024656 ≤ envelopePrefix F 3016464+(7415986941:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3016465) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C387.data C387.counts_checked C387.bounds_checked C387.weighted_checked
  have h4 : envelopePrefix F 3032848 ≤ envelopePrefix F 3024656+(7665333875:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3024657) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C388.data C388.counts_checked C388.bounds_checked C388.weighted_checked
  have h5 : envelopePrefix F 3041040 ≤ envelopePrefix F 3032848+(7455306202:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3032849) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C389.data C389.counts_checked C389.bounds_checked C389.weighted_checked
  have h6 : envelopePrefix F 3049232 ≤ envelopePrefix F 3041040+(7578973906:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3041041) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C390.data C390.counts_checked C390.bounds_checked C390.weighted_checked
  have h7 : envelopePrefix F 3057424 ≤ envelopePrefix F 3049232+(7411544254:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3049233) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C391.data C391.counts_checked C391.bounds_checked C391.weighted_checked
  have h8 : envelopePrefix F 3065616 ≤ envelopePrefix F 3057424+(7355464862:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3057425) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C392.data C392.counts_checked C392.bounds_checked C392.weighted_checked
  have h9 : envelopePrefix F 3073808 ≤ envelopePrefix F 3065616+(7726192900:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3065617) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C393.data C393.counts_checked C393.bounds_checked C393.weighted_checked
  have h10 : envelopePrefix F 3082000 ≤ envelopePrefix F 3073808+(7958249594:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3073809) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C394.data C394.counts_checked C394.bounds_checked C394.weighted_checked
  have h11 : envelopePrefix F 3090192 ≤ envelopePrefix F 3082000+(7626503661:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3082001) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C395.data C395.counts_checked C395.bounds_checked C395.weighted_checked
  have h12 : envelopePrefix F 3098384 ≤ envelopePrefix F 3090192+(7392698587:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3090193) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C396.data C396.counts_checked C396.bounds_checked C396.weighted_checked
  have h13 : envelopePrefix F 3106576 ≤ envelopePrefix F 3098384+(7391410777:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3098385) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C397.data C397.counts_checked C397.bounds_checked C397.weighted_checked
  have h14 : envelopePrefix F 3114768 ≤ envelopePrefix F 3106576+(7472498872:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3106577) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C398.data C398.counts_checked C398.bounds_checked C398.weighted_checked
  have h15 : envelopePrefix F 3122960 ≤ envelopePrefix F 3114768+(7648330033:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3114769) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C399.data C399.counts_checked C399.bounds_checked C399.weighted_checked
  have h16 : envelopePrefix F 3131152 ≤ envelopePrefix F 3122960+(7470081103:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3122961) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C400.data C400.counts_checked C400.bounds_checked C400.weighted_checked
  have h17 : envelopePrefix F 3139344 ≤ envelopePrefix F 3131152+(7225157123:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3131153) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C401.data C401.counts_checked C401.bounds_checked C401.weighted_checked
  have h18 : envelopePrefix F 3147536 ≤ envelopePrefix F 3139344+(7332784262:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3139345) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C402.data C402.counts_checked C402.bounds_checked C402.weighted_checked
  have h19 : envelopePrefix F 3155728 ≤ envelopePrefix F 3147536+(7602005383:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3147537) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C403.data C403.counts_checked C403.bounds_checked C403.weighted_checked
  have h20 : envelopePrefix F 3163920 ≤ envelopePrefix F 3155728+(7209936313:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3155729) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C404.data C404.counts_checked C404.bounds_checked C404.weighted_checked
  have h21 : envelopePrefix F 3172112 ≤ envelopePrefix F 3163920+(7639744585:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3163921) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C405.data C405.counts_checked C405.bounds_checked C405.weighted_checked
  have h22 : envelopePrefix F 3180304 ≤ envelopePrefix F 3172112+(7088144638:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3172113) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C406.data C406.counts_checked C406.bounds_checked C406.weighted_checked
  have h23 : envelopePrefix F 3188496 ≤ envelopePrefix F 3180304+(7529955504:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3180305) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C407.data C407.counts_checked C407.bounds_checked C407.weighted_checked
  have h24 : envelopePrefix F 3196688 ≤ envelopePrefix F 3188496+(7461966731:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3188497) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C408.data C408.counts_checked C408.bounds_checked C408.weighted_checked
  have h25 : envelopePrefix F 3204880 ≤ envelopePrefix F 3196688+(7581111108:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3196689) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C409.data C409.counts_checked C409.bounds_checked C409.weighted_checked
  have h26 : envelopePrefix F 3213072 ≤ envelopePrefix F 3204880+(7433282960:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3204881) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C410.data C410.counts_checked C410.bounds_checked C410.weighted_checked
  have h27 : envelopePrefix F 3221264 ≤ envelopePrefix F 3213072+(7286146356:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3213073) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C411.data C411.counts_checked C411.bounds_checked C411.weighted_checked
  have h28 : envelopePrefix F 3229456 ≤ envelopePrefix F 3221264+(7378328348:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3221265) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C412.data C412.counts_checked C412.bounds_checked C412.weighted_checked
  have h29 : envelopePrefix F 3237648 ≤ envelopePrefix F 3229456+(7403891072:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3229457) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C413.data C413.counts_checked C413.bounds_checked C413.weighted_checked
  have h30 : envelopePrefix F 3245840 ≤ envelopePrefix F 3237648+(7006735135:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3237649) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C414.data C414.counts_checked C414.bounds_checked C414.weighted_checked
  have h31 : envelopePrefix F 3254032 ≤ envelopePrefix F 3245840+(7125521904:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3245841) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C415.data C415.counts_checked C415.bounds_checked C415.weighted_checked
  have m0 : envelopePrefix F 3008272 ≤ envelopePrefix F 2991888+(15622428863:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 3024656 ≤ envelopePrefix F 3008272+(15014754371:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 3041040 ≤ envelopePrefix F 3024656+(15120640077:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 3057424 ≤ envelopePrefix F 3041040+(14990518160:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 3073808 ≤ envelopePrefix F 3057424+(15081657762:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 3090192 ≤ envelopePrefix F 3073808+(15584753255:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 3106576 ≤ envelopePrefix F 3090192+(14784109364:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 3122960 ≤ envelopePrefix F 3106576+(15120828905:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 3139344 ≤ envelopePrefix F 3122960+(14695238226:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 3155728 ≤ envelopePrefix F 3139344+(14934789645:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 3172112 ≤ envelopePrefix F 3155728+(14849680898:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 3188496 ≤ envelopePrefix F 3172112+(14618100142:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 3204880 ≤ envelopePrefix F 3188496+(15043077839:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 3221264 ≤ envelopePrefix F 3204880+(14719429316:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 3237648 ≤ envelopePrefix F 3221264+(14782219420:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 3254032 ≤ envelopePrefix F 3237648+(14132257039:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 3024656 ≤ envelopePrefix F 2991888+(30637183234:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 3057424 ≤ envelopePrefix F 3024656+(30111158237:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 3090192 ≤ envelopePrefix F 3057424+(30666411017:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 3122960 ≤ envelopePrefix F 3090192+(29904938269:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 3155728 ≤ envelopePrefix F 3122960+(29630027871:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 3188496 ≤ envelopePrefix F 3155728+(29467781040:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 3221264 ≤ envelopePrefix F 3188496+(29762507155:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 3254032 ≤ envelopePrefix F 3221264+(28914476459:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 3057424 ≤ envelopePrefix F 2991888+(60748341471:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 3122960 ≤ envelopePrefix F 3057424+(60571349286:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 3188496 ≤ envelopePrefix F 3122960+(59097808911:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 3254032 ≤ envelopePrefix F 3188496+(58676983614:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 3122960 ≤ envelopePrefix F 2991888+(121319690757:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 3254032 ≤ envelopePrefix F 3122960+(117774792525:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 3254032 ≤ envelopePrefix F 2991888+(239094483282:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup12_bound
end ChenEffective.H10Band
end
