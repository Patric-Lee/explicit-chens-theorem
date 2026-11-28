import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C288
import GRHQuarterCertificates.C289
import GRHQuarterCertificates.C290
import GRHQuarterCertificates.C291
import GRHQuarterCertificates.C292
import GRHQuarterCertificates.C293
import GRHQuarterCertificates.C294
import GRHQuarterCertificates.C295
import GRHQuarterCertificates.C296
import GRHQuarterCertificates.C297
import GRHQuarterCertificates.C298
import GRHQuarterCertificates.C299
import GRHQuarterCertificates.C300
import GRHQuarterCertificates.C301
import GRHQuarterCertificates.C302
import GRHQuarterCertificates.C303
import GRHQuarterCertificates.C304
import GRHQuarterCertificates.C305
import GRHQuarterCertificates.C306
import GRHQuarterCertificates.C307
import GRHQuarterCertificates.C308
import GRHQuarterCertificates.C309
import GRHQuarterCertificates.C310
import GRHQuarterCertificates.C311
import GRHQuarterCertificates.C312
import GRHQuarterCertificates.C313
import GRHQuarterCertificates.C314
import GRHQuarterCertificates.C315
import GRHQuarterCertificates.C316
import GRHQuarterCertificates.C317
import GRHQuarterCertificates.C318
import GRHQuarterCertificates.C319
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup09_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 2467600 ≤ envelopePrefix F 2205456+(301826114387:ℝ)/denominator := by
  have h0 : envelopePrefix F 2213648 ≤ envelopePrefix F 2205456+(10116060669:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2205457) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C288.data C288.counts_checked C288.bounds_checked C288.weighted_checked
  have h1 : envelopePrefix F 2221840 ≤ envelopePrefix F 2213648+(9244201821:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2213649) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C289.data C289.counts_checked C289.bounds_checked C289.weighted_checked
  have h2 : envelopePrefix F 2230032 ≤ envelopePrefix F 2221840+(10182679641:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2221841) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C290.data C290.counts_checked C290.bounds_checked C290.weighted_checked
  have h3 : envelopePrefix F 2238224 ≤ envelopePrefix F 2230032+(9787627602:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2230033) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C291.data C291.counts_checked C291.bounds_checked C291.weighted_checked
  have h4 : envelopePrefix F 2246416 ≤ envelopePrefix F 2238224+(9743197511:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2238225) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C292.data C292.counts_checked C292.bounds_checked C292.weighted_checked
  have h5 : envelopePrefix F 2254608 ≤ envelopePrefix F 2246416+(9490655752:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2246417) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C293.data C293.counts_checked C293.bounds_checked C293.weighted_checked
  have h6 : envelopePrefix F 2262800 ≤ envelopePrefix F 2254608+(9950746663:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2254609) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C294.data C294.counts_checked C294.bounds_checked C294.weighted_checked
  have h7 : envelopePrefix F 2270992 ≤ envelopePrefix F 2262800+(10113512266:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2262801) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C295.data C295.counts_checked C295.bounds_checked C295.weighted_checked
  have h8 : envelopePrefix F 2279184 ≤ envelopePrefix F 2270992+(9827868292:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2270993) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C296.data C296.counts_checked C296.bounds_checked C296.weighted_checked
  have h9 : envelopePrefix F 2287376 ≤ envelopePrefix F 2279184+(9164669709:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2279185) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C297.data C297.counts_checked C297.bounds_checked C297.weighted_checked
  have h10 : envelopePrefix F 2295568 ≤ envelopePrefix F 2287376+(9586238475:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2287377) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C298.data C298.counts_checked C298.bounds_checked C298.weighted_checked
  have h11 : envelopePrefix F 2303760 ≤ envelopePrefix F 2295568+(9714433677:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2295569) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C299.data C299.counts_checked C299.bounds_checked C299.weighted_checked
  have h12 : envelopePrefix F 2311952 ≤ envelopePrefix F 2303760+(9620117981:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2303761) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C300.data C300.counts_checked C300.bounds_checked C300.weighted_checked
  have h13 : envelopePrefix F 2320144 ≤ envelopePrefix F 2311952+(9067174027:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2311953) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C301.data C301.counts_checked C301.bounds_checked C301.weighted_checked
  have h14 : envelopePrefix F 2328336 ≤ envelopePrefix F 2320144+(9416448394:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2320145) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C302.data C302.counts_checked C302.bounds_checked C302.weighted_checked
  have h15 : envelopePrefix F 2336528 ≤ envelopePrefix F 2328336+(9425422690:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2328337) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C303.data C303.counts_checked C303.bounds_checked C303.weighted_checked
  have h16 : envelopePrefix F 2344720 ≤ envelopePrefix F 2336528+(9316444247:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2336529) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C304.data C304.counts_checked C304.bounds_checked C304.weighted_checked
  have h17 : envelopePrefix F 2352912 ≤ envelopePrefix F 2344720+(9090059324:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2344721) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C305.data C305.counts_checked C305.bounds_checked C305.weighted_checked
  have h18 : envelopePrefix F 2361104 ≤ envelopePrefix F 2352912+(9402291180:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2352913) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C306.data C306.counts_checked C306.bounds_checked C306.weighted_checked
  have h19 : envelopePrefix F 2369296 ≤ envelopePrefix F 2361104+(9562179653:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2361105) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C307.data C307.counts_checked C307.bounds_checked C307.weighted_checked
  have h20 : envelopePrefix F 2377488 ≤ envelopePrefix F 2369296+(9136446260:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2369297) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C308.data C308.counts_checked C308.bounds_checked C308.weighted_checked
  have h21 : envelopePrefix F 2385680 ≤ envelopePrefix F 2377488+(9163018793:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2377489) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C309.data C309.counts_checked C309.bounds_checked C309.weighted_checked
  have h22 : envelopePrefix F 2393872 ≤ envelopePrefix F 2385680+(9455579986:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2385681) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C310.data C310.counts_checked C310.bounds_checked C310.weighted_checked
  have h23 : envelopePrefix F 2402064 ≤ envelopePrefix F 2393872+(9215563829:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2393873) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C311.data C311.counts_checked C311.bounds_checked C311.weighted_checked
  have h24 : envelopePrefix F 2410256 ≤ envelopePrefix F 2402064+(9026882455:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2402065) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C312.data C312.counts_checked C312.bounds_checked C312.weighted_checked
  have h25 : envelopePrefix F 2418448 ≤ envelopePrefix F 2410256+(9465187609:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2410257) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C313.data C313.counts_checked C313.bounds_checked C313.weighted_checked
  have h26 : envelopePrefix F 2426640 ≤ envelopePrefix F 2418448+(9112262298:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2418449) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C314.data C314.counts_checked C314.bounds_checked C314.weighted_checked
  have h27 : envelopePrefix F 2434832 ≤ envelopePrefix F 2426640+(8957988079:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2426641) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C315.data C315.counts_checked C315.bounds_checked C315.weighted_checked
  have h28 : envelopePrefix F 2443024 ≤ envelopePrefix F 2434832+(8968135155:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2434833) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C316.data C316.counts_checked C316.bounds_checked C316.weighted_checked
  have h29 : envelopePrefix F 2451216 ≤ envelopePrefix F 2443024+(9076433868:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2443025) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C317.data C317.counts_checked C317.bounds_checked C317.weighted_checked
  have h30 : envelopePrefix F 2459408 ≤ envelopePrefix F 2451216+(9363084069:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2451217) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C318.data C318.counts_checked C318.bounds_checked C318.weighted_checked
  have h31 : envelopePrefix F 2467600 ≤ envelopePrefix F 2459408+(9063502412:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2459409) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C319.data C319.counts_checked C319.bounds_checked C319.weighted_checked
  have m0 : envelopePrefix F 2221840 ≤ envelopePrefix F 2205456+(19360262490:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 2238224 ≤ envelopePrefix F 2221840+(19970307243:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 2254608 ≤ envelopePrefix F 2238224+(19233853263:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 2270992 ≤ envelopePrefix F 2254608+(20064258929:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 2287376 ≤ envelopePrefix F 2270992+(18992538001:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 2303760 ≤ envelopePrefix F 2287376+(19300672152:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 2320144 ≤ envelopePrefix F 2303760+(18687292008:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 2336528 ≤ envelopePrefix F 2320144+(18841871084:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 2352912 ≤ envelopePrefix F 2336528+(18406503571:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 2369296 ≤ envelopePrefix F 2352912+(18964470833:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 2385680 ≤ envelopePrefix F 2369296+(18299465053:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 2402064 ≤ envelopePrefix F 2385680+(18671143815:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 2418448 ≤ envelopePrefix F 2402064+(18492070064:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 2434832 ≤ envelopePrefix F 2418448+(18070250377:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 2451216 ≤ envelopePrefix F 2434832+(18044569023:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 2467600 ≤ envelopePrefix F 2451216+(18426586481:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 2238224 ≤ envelopePrefix F 2205456+(39330569733:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 2270992 ≤ envelopePrefix F 2238224+(39298112192:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 2303760 ≤ envelopePrefix F 2270992+(38293210153:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 2336528 ≤ envelopePrefix F 2303760+(37529163092:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 2369296 ≤ envelopePrefix F 2336528+(37370974404:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 2402064 ≤ envelopePrefix F 2369296+(36970608868:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 2434832 ≤ envelopePrefix F 2402064+(36562320441:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 2467600 ≤ envelopePrefix F 2434832+(36471155504:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 2270992 ≤ envelopePrefix F 2205456+(78628681925:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 2336528 ≤ envelopePrefix F 2270992+(75822373245:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 2402064 ≤ envelopePrefix F 2336528+(74341583272:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 2467600 ≤ envelopePrefix F 2402064+(73033475945:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 2336528 ≤ envelopePrefix F 2205456+(154451055170:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 2467600 ≤ envelopePrefix F 2336528+(147375059217:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 2467600 ≤ envelopePrefix F 2205456+(301826114387:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup09_bound
end ChenEffective.H10Band
end
