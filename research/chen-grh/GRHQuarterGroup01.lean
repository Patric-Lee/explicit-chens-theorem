import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C032
import GRHQuarterCertificates.C033
import GRHQuarterCertificates.C034
import GRHQuarterCertificates.C035
import GRHQuarterCertificates.C036
import GRHQuarterCertificates.C037
import GRHQuarterCertificates.C038
import GRHQuarterCertificates.C039
import GRHQuarterCertificates.C040
import GRHQuarterCertificates.C041
import GRHQuarterCertificates.C042
import GRHQuarterCertificates.C043
import GRHQuarterCertificates.C044
import GRHQuarterCertificates.C045
import GRHQuarterCertificates.C046
import GRHQuarterCertificates.C047
import GRHQuarterCertificates.C048
import GRHQuarterCertificates.C049
import GRHQuarterCertificates.C050
import GRHQuarterCertificates.C051
import GRHQuarterCertificates.C052
import GRHQuarterCertificates.C053
import GRHQuarterCertificates.C054
import GRHQuarterCertificates.C055
import GRHQuarterCertificates.C056
import GRHQuarterCertificates.C057
import GRHQuarterCertificates.C058
import GRHQuarterCertificates.C059
import GRHQuarterCertificates.C060
import GRHQuarterCertificates.C061
import GRHQuarterCertificates.C062
import GRHQuarterCertificates.C063
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup01_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 370448 ≤ envelopePrefix F 108304+(2154419293111:ℝ)/denominator := by
  have h0 : envelopePrefix F 116496 ≤ envelopePrefix F 108304+(115030625984:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=108305) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C032.data C032.counts_checked C032.bounds_checked C032.weighted_checked
  have h1 : envelopePrefix F 124688 ≤ envelopePrefix F 116496+(109583941904:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=116497) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C033.data C033.counts_checked C033.bounds_checked C033.weighted_checked
  have h2 : envelopePrefix F 132880 ≤ envelopePrefix F 124688+(103580570053:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=124689) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C034.data C034.counts_checked C034.bounds_checked C034.weighted_checked
  have h3 : envelopePrefix F 141072 ≤ envelopePrefix F 132880+(99030972036:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=132881) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C035.data C035.counts_checked C035.bounds_checked C035.weighted_checked
  have h4 : envelopePrefix F 149264 ≤ envelopePrefix F 141072+(92758642627:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=141073) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C036.data C036.counts_checked C036.bounds_checked C036.weighted_checked
  have h5 : envelopePrefix F 157456 ≤ envelopePrefix F 149264+(90479408628:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=149265) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C037.data C037.counts_checked C037.bounds_checked C037.weighted_checked
  have h6 : envelopePrefix F 165648 ≤ envelopePrefix F 157456+(83737126918:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=157457) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C038.data C038.counts_checked C038.bounds_checked C038.weighted_checked
  have h7 : envelopePrefix F 173840 ≤ envelopePrefix F 165648+(81399321294:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=165649) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C039.data C039.counts_checked C039.bounds_checked C039.weighted_checked
  have h8 : envelopePrefix F 182032 ≤ envelopePrefix F 173840+(78821502812:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=173841) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C040.data C040.counts_checked C040.bounds_checked C040.weighted_checked
  have h9 : envelopePrefix F 190224 ≤ envelopePrefix F 182032+(77341594290:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=182033) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C041.data C041.counts_checked C041.bounds_checked C041.weighted_checked
  have h10 : envelopePrefix F 198416 ≤ envelopePrefix F 190224+(73558536729:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=190225) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C042.data C042.counts_checked C042.bounds_checked C042.weighted_checked
  have h11 : envelopePrefix F 206608 ≤ envelopePrefix F 198416+(70246988858:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=198417) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C043.data C043.counts_checked C043.bounds_checked C043.weighted_checked
  have h12 : envelopePrefix F 214800 ≤ envelopePrefix F 206608+(69641075698:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=206609) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C044.data C044.counts_checked C044.bounds_checked C044.weighted_checked
  have h13 : envelopePrefix F 222992 ≤ envelopePrefix F 214800+(65757884155:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=214801) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C045.data C045.counts_checked C045.bounds_checked C045.weighted_checked
  have h14 : envelopePrefix F 231184 ≤ envelopePrefix F 222992+(65630794853:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=222993) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C046.data C046.counts_checked C046.bounds_checked C046.weighted_checked
  have h15 : envelopePrefix F 239376 ≤ envelopePrefix F 231184+(60131804160:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=231185) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C047.data C047.counts_checked C047.bounds_checked C047.weighted_checked
  have h16 : envelopePrefix F 247568 ≤ envelopePrefix F 239376+(61564686974:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=239377) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C048.data C048.counts_checked C048.bounds_checked C048.weighted_checked
  have h17 : envelopePrefix F 255760 ≤ envelopePrefix F 247568+(59964389192:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=247569) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C049.data C049.counts_checked C049.bounds_checked C049.weighted_checked
  have h18 : envelopePrefix F 263952 ≤ envelopePrefix F 255760+(56424922791:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=255761) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C050.data C050.counts_checked C050.bounds_checked C050.weighted_checked
  have h19 : envelopePrefix F 272144 ≤ envelopePrefix F 263952+(57192089872:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=263953) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C051.data C051.counts_checked C051.bounds_checked C051.weighted_checked
  have h20 : envelopePrefix F 280336 ≤ envelopePrefix F 272144+(54155665552:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=272145) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C052.data C052.counts_checked C052.bounds_checked C052.weighted_checked
  have h21 : envelopePrefix F 288528 ≤ envelopePrefix F 280336+(52585000492:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=280337) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C053.data C053.counts_checked C053.bounds_checked C053.weighted_checked
  have h22 : envelopePrefix F 296720 ≤ envelopePrefix F 288528+(51949808645:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=288529) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C054.data C054.counts_checked C054.bounds_checked C054.weighted_checked
  have h23 : envelopePrefix F 304912 ≤ envelopePrefix F 296720+(51413777452:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=296721) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C055.data C055.counts_checked C055.bounds_checked C055.weighted_checked
  have h24 : envelopePrefix F 313104 ≤ envelopePrefix F 304912+(49171356691:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=304913) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C056.data C056.counts_checked C056.bounds_checked C056.weighted_checked
  have h25 : envelopePrefix F 321296 ≤ envelopePrefix F 313104+(50557057142:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=313105) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C057.data C057.counts_checked C057.bounds_checked C057.weighted_checked
  have h26 : envelopePrefix F 329488 ≤ envelopePrefix F 321296+(48339979174:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=321297) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C058.data C058.counts_checked C058.bounds_checked C058.weighted_checked
  have h27 : envelopePrefix F 337680 ≤ envelopePrefix F 329488+(47226610298:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=329489) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C059.data C059.counts_checked C059.bounds_checked C059.weighted_checked
  have h28 : envelopePrefix F 345872 ≤ envelopePrefix F 337680+(45513969712:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=337681) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C060.data C060.counts_checked C060.bounds_checked C060.weighted_checked
  have h29 : envelopePrefix F 354064 ≤ envelopePrefix F 345872+(45766639414:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=345873) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C061.data C061.counts_checked C061.bounds_checked C061.weighted_checked
  have h30 : envelopePrefix F 362256 ≤ envelopePrefix F 354064+(43190014413:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=354065) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C062.data C062.counts_checked C062.bounds_checked C062.weighted_checked
  have h31 : envelopePrefix F 370448 ≤ envelopePrefix F 362256+(42672534298:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=362257) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C063.data C063.counts_checked C063.bounds_checked C063.weighted_checked
  have m0 : envelopePrefix F 124688 ≤ envelopePrefix F 108304+(224614567888:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 141072 ≤ envelopePrefix F 124688+(202611542089:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 157456 ≤ envelopePrefix F 141072+(183238051255:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 173840 ≤ envelopePrefix F 157456+(165136448212:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 190224 ≤ envelopePrefix F 173840+(156163097102:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 206608 ≤ envelopePrefix F 190224+(143805525587:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 222992 ≤ envelopePrefix F 206608+(135398959853:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 239376 ≤ envelopePrefix F 222992+(125762599013:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 255760 ≤ envelopePrefix F 239376+(121529076166:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 272144 ≤ envelopePrefix F 255760+(113617012663:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 288528 ≤ envelopePrefix F 272144+(106740666044:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 304912 ≤ envelopePrefix F 288528+(103363586097:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 321296 ≤ envelopePrefix F 304912+(99728413833:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 337680 ≤ envelopePrefix F 321296+(95566589472:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 354064 ≤ envelopePrefix F 337680+(91280609126:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 370448 ≤ envelopePrefix F 354064+(85862548711:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 141072 ≤ envelopePrefix F 108304+(427226109977:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 173840 ≤ envelopePrefix F 141072+(348374499467:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 206608 ≤ envelopePrefix F 173840+(299968622689:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 239376 ≤ envelopePrefix F 206608+(261161558866:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 272144 ≤ envelopePrefix F 239376+(235146088829:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 304912 ≤ envelopePrefix F 272144+(210104252141:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 337680 ≤ envelopePrefix F 304912+(195295003305:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 370448 ≤ envelopePrefix F 337680+(177143157837:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 173840 ≤ envelopePrefix F 108304+(775600609444:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 239376 ≤ envelopePrefix F 173840+(561130181555:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 304912 ≤ envelopePrefix F 239376+(445250340970:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 370448 ≤ envelopePrefix F 304912+(372438161142:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 239376 ≤ envelopePrefix F 108304+(1336730790999:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 370448 ≤ envelopePrefix F 239376+(817688502112:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 370448 ≤ envelopePrefix F 108304+(2154419293111:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup01_bound
end ChenEffective.H10Band
end
