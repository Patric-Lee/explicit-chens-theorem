import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C256
import GRHQuarterCertificates.C257
import GRHQuarterCertificates.C258
import GRHQuarterCertificates.C259
import GRHQuarterCertificates.C260
import GRHQuarterCertificates.C261
import GRHQuarterCertificates.C262
import GRHQuarterCertificates.C263
import GRHQuarterCertificates.C264
import GRHQuarterCertificates.C265
import GRHQuarterCertificates.C266
import GRHQuarterCertificates.C267
import GRHQuarterCertificates.C268
import GRHQuarterCertificates.C269
import GRHQuarterCertificates.C270
import GRHQuarterCertificates.C271
import GRHQuarterCertificates.C272
import GRHQuarterCertificates.C273
import GRHQuarterCertificates.C274
import GRHQuarterCertificates.C275
import GRHQuarterCertificates.C276
import GRHQuarterCertificates.C277
import GRHQuarterCertificates.C278
import GRHQuarterCertificates.C279
import GRHQuarterCertificates.C280
import GRHQuarterCertificates.C281
import GRHQuarterCertificates.C282
import GRHQuarterCertificates.C283
import GRHQuarterCertificates.C284
import GRHQuarterCertificates.C285
import GRHQuarterCertificates.C286
import GRHQuarterCertificates.C287
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup08_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 2205456 ≤ envelopePrefix F 1943312+(332879413379:ℝ)/denominator := by
  have h0 : envelopePrefix F 1951504 ≤ envelopePrefix F 1943312+(10888768635:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1943313) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C256.data C256.counts_checked C256.bounds_checked C256.weighted_checked
  have h1 : envelopePrefix F 1959696 ≤ envelopePrefix F 1951504+(10777254678:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1951505) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C257.data C257.counts_checked C257.bounds_checked C257.weighted_checked
  have h2 : envelopePrefix F 1967888 ≤ envelopePrefix F 1959696+(10782113596:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1959697) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C258.data C258.counts_checked C258.bounds_checked C258.weighted_checked
  have h3 : envelopePrefix F 1976080 ≤ envelopePrefix F 1967888+(10229965345:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1967889) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C259.data C259.counts_checked C259.bounds_checked C259.weighted_checked
  have h4 : envelopePrefix F 1984272 ≤ envelopePrefix F 1976080+(11212070804:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1976081) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C260.data C260.counts_checked C260.bounds_checked C260.weighted_checked
  have h5 : envelopePrefix F 1992464 ≤ envelopePrefix F 1984272+(10605093654:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1984273) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C261.data C261.counts_checked C261.bounds_checked C261.weighted_checked
  have h6 : envelopePrefix F 2000656 ≤ envelopePrefix F 1992464+(11124080755:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1992465) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C262.data C262.counts_checked C262.bounds_checked C262.weighted_checked
  have h7 : envelopePrefix F 2008848 ≤ envelopePrefix F 2000656+(10975731038:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2000657) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C263.data C263.counts_checked C263.bounds_checked C263.weighted_checked
  have h8 : envelopePrefix F 2017040 ≤ envelopePrefix F 2008848+(10791154588:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2008849) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C264.data C264.counts_checked C264.bounds_checked C264.weighted_checked
  have h9 : envelopePrefix F 2025232 ≤ envelopePrefix F 2017040+(10381995001:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2017041) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C265.data C265.counts_checked C265.bounds_checked C265.weighted_checked
  have h10 : envelopePrefix F 2033424 ≤ envelopePrefix F 2025232+(10951330897:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2025233) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C266.data C266.counts_checked C266.bounds_checked C266.weighted_checked
  have h11 : envelopePrefix F 2041616 ≤ envelopePrefix F 2033424+(10300651518:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2033425) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C267.data C267.counts_checked C267.bounds_checked C267.weighted_checked
  have h12 : envelopePrefix F 2049808 ≤ envelopePrefix F 2041616+(10363238371:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2041617) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C268.data C268.counts_checked C268.bounds_checked C268.weighted_checked
  have h13 : envelopePrefix F 2058000 ≤ envelopePrefix F 2049808+(10480656240:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2049809) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C269.data C269.counts_checked C269.bounds_checked C269.weighted_checked
  have h14 : envelopePrefix F 2066192 ≤ envelopePrefix F 2058000+(10672208541:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2058001) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C270.data C270.counts_checked C270.bounds_checked C270.weighted_checked
  have h15 : envelopePrefix F 2074384 ≤ envelopePrefix F 2066192+(10270546308:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2066193) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C271.data C271.counts_checked C271.bounds_checked C271.weighted_checked
  have h16 : envelopePrefix F 2082576 ≤ envelopePrefix F 2074384+(10037270647:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2074385) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C272.data C272.counts_checked C272.bounds_checked C272.weighted_checked
  have h17 : envelopePrefix F 2090768 ≤ envelopePrefix F 2082576+(10596436586:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2082577) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C273.data C273.counts_checked C273.bounds_checked C273.weighted_checked
  have h18 : envelopePrefix F 2098960 ≤ envelopePrefix F 2090768+(10143255598:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2090769) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C274.data C274.counts_checked C274.bounds_checked C274.weighted_checked
  have h19 : envelopePrefix F 2107152 ≤ envelopePrefix F 2098960+(10588957672:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2098961) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C275.data C275.counts_checked C275.bounds_checked C275.weighted_checked
  have h20 : envelopePrefix F 2115344 ≤ envelopePrefix F 2107152+(10138679851:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2107153) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C276.data C276.counts_checked C276.bounds_checked C276.weighted_checked
  have h21 : envelopePrefix F 2123536 ≤ envelopePrefix F 2115344+(10073281773:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2115345) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C277.data C277.counts_checked C277.bounds_checked C277.weighted_checked
  have h22 : envelopePrefix F 2131728 ≤ envelopePrefix F 2123536+(10352201073:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2123537) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C278.data C278.counts_checked C278.bounds_checked C278.weighted_checked
  have h23 : envelopePrefix F 2139920 ≤ envelopePrefix F 2131728+(9997086454:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2131729) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C279.data C279.counts_checked C279.bounds_checked C279.weighted_checked
  have h24 : envelopePrefix F 2148112 ≤ envelopePrefix F 2139920+(10383251059:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2139921) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C280.data C280.counts_checked C280.bounds_checked C280.weighted_checked
  have h25 : envelopePrefix F 2156304 ≤ envelopePrefix F 2148112+(10065595306:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2148113) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C281.data C281.counts_checked C281.bounds_checked C281.weighted_checked
  have h26 : envelopePrefix F 2164496 ≤ envelopePrefix F 2156304+(10431747285:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2156305) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C282.data C282.counts_checked C282.bounds_checked C282.weighted_checked
  have h27 : envelopePrefix F 2172688 ≤ envelopePrefix F 2164496+(9793838066:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2164497) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C283.data C283.counts_checked C283.bounds_checked C283.weighted_checked
  have h28 : envelopePrefix F 2180880 ≤ envelopePrefix F 2172688+(10069597122:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2172689) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C284.data C284.counts_checked C284.bounds_checked C284.weighted_checked
  have h29 : envelopePrefix F 2189072 ≤ envelopePrefix F 2180880+(9845434687:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2180881) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C285.data C285.counts_checked C285.bounds_checked C285.weighted_checked
  have h30 : envelopePrefix F 2197264 ≤ envelopePrefix F 2189072+(9924586885:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2189073) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C286.data C286.counts_checked C286.bounds_checked C286.weighted_checked
  have h31 : envelopePrefix F 2205456 ≤ envelopePrefix F 2197264+(9631333346:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2197265) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C287.data C287.counts_checked C287.bounds_checked C287.weighted_checked
  have m0 : envelopePrefix F 1959696 ≤ envelopePrefix F 1943312+(21666023313:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 1976080 ≤ envelopePrefix F 1959696+(21012078941:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 1992464 ≤ envelopePrefix F 1976080+(21817164458:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 2008848 ≤ envelopePrefix F 1992464+(22099811793:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 2025232 ≤ envelopePrefix F 2008848+(21173149589:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 2041616 ≤ envelopePrefix F 2025232+(21251982415:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 2058000 ≤ envelopePrefix F 2041616+(20843894611:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 2074384 ≤ envelopePrefix F 2058000+(20942754849:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 2090768 ≤ envelopePrefix F 2074384+(20633707233:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 2107152 ≤ envelopePrefix F 2090768+(20732213270:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 2123536 ≤ envelopePrefix F 2107152+(20211961624:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 2139920 ≤ envelopePrefix F 2123536+(20349287527:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 2156304 ≤ envelopePrefix F 2139920+(20448846365:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 2172688 ≤ envelopePrefix F 2156304+(20225585351:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 2189072 ≤ envelopePrefix F 2172688+(19915031809:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 2205456 ≤ envelopePrefix F 2189072+(19555920231:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 1976080 ≤ envelopePrefix F 1943312+(42678102254:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 2008848 ≤ envelopePrefix F 1976080+(43916976251:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 2041616 ≤ envelopePrefix F 2008848+(42425132004:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 2074384 ≤ envelopePrefix F 2041616+(41786649460:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 2107152 ≤ envelopePrefix F 2074384+(41365920503:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 2139920 ≤ envelopePrefix F 2107152+(40561249151:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 2172688 ≤ envelopePrefix F 2139920+(40674431716:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 2205456 ≤ envelopePrefix F 2172688+(39470952040:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 2008848 ≤ envelopePrefix F 1943312+(86595078505:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 2074384 ≤ envelopePrefix F 2008848+(84211781464:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 2139920 ≤ envelopePrefix F 2074384+(81927169654:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 2205456 ≤ envelopePrefix F 2139920+(80145383756:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 2074384 ≤ envelopePrefix F 1943312+(170806859969:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 2205456 ≤ envelopePrefix F 2074384+(162072553410:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 2205456 ≤ envelopePrefix F 1943312+(332879413379:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup08_bound
end ChenEffective.H10Band
end
