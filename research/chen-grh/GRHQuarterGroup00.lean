import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C000
import GRHQuarterCertificates.C001
import GRHQuarterCertificates.C002
import GRHQuarterCertificates.C003
import GRHQuarterCertificates.C004
import GRHQuarterCertificates.C005
import GRHQuarterCertificates.C006
import GRHQuarterCertificates.C007
import GRHQuarterCertificates.C008
import GRHQuarterCertificates.C009
import GRHQuarterCertificates.C010
import GRHQuarterCertificates.C011
import GRHQuarterCertificates.C012
import GRHQuarterCertificates.C013
import GRHQuarterCertificates.C014
import GRHQuarterCertificates.C015
import GRHQuarterCertificates.C016
import GRHQuarterCertificates.C017
import GRHQuarterCertificates.C018
import GRHQuarterCertificates.C019
import GRHQuarterCertificates.C020
import GRHQuarterCertificates.C021
import GRHQuarterCertificates.C022
import GRHQuarterCertificates.C023
import GRHQuarterCertificates.C024
import GRHQuarterCertificates.C025
import GRHQuarterCertificates.C026
import GRHQuarterCertificates.C027
import GRHQuarterCertificates.C028
import GRHQuarterCertificates.C029
import GRHQuarterCertificates.C030
import GRHQuarterCertificates.C031
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup00_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 108304 ≤ envelopePrefix F 2+(10084194995817:ℝ)/denominator := by
  have h0 : envelopePrefix F 514 ≤ envelopePrefix F 2+(4291331490302:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C000.data C000.counts_checked C000.bounds_checked C000.weighted_checked
  have h1 : envelopePrefix F 1026 ≤ envelopePrefix F 514+(530085877764:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=515) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C001.data C001.counts_checked C001.bounds_checked C001.weighted_checked
  have h2 : envelopePrefix F 1538 ≤ envelopePrefix F 1026+(333171623971:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1027) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C002.data C002.counts_checked C002.bounds_checked C002.weighted_checked
  have h3 : envelopePrefix F 2050 ≤ envelopePrefix F 1538+(247177827553:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1539) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C003.data C003.counts_checked C003.bounds_checked C003.weighted_checked
  have h4 : envelopePrefix F 2562 ≤ envelopePrefix F 2050+(200818547116:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2051) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C004.data C004.counts_checked C004.bounds_checked C004.weighted_checked
  have h5 : envelopePrefix F 3074 ≤ envelopePrefix F 2562+(167406332119:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=2563) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C005.data C005.counts_checked C005.bounds_checked C005.weighted_checked
  have h6 : envelopePrefix F 3586 ≤ envelopePrefix F 3074+(144692120775:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3075) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C006.data C006.counts_checked C006.bounds_checked C006.weighted_checked
  have h7 : envelopePrefix F 4098 ≤ envelopePrefix F 3586+(128300099082:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3587) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C007.data C007.counts_checked C007.bounds_checked C007.weighted_checked
  have h8 : envelopePrefix F 4610 ≤ envelopePrefix F 4098+(111202468519:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=4099) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C008.data C008.counts_checked C008.bounds_checked C008.weighted_checked
  have h9 : envelopePrefix F 5122 ≤ envelopePrefix F 4610+(107293830705:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=4611) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C009.data C009.counts_checked C009.bounds_checked C009.weighted_checked
  have h10 : envelopePrefix F 5634 ≤ envelopePrefix F 5122+(86749347178:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=5123) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C010.data C010.counts_checked C010.bounds_checked C010.weighted_checked
  have h11 : envelopePrefix F 6146 ≤ envelopePrefix F 5634+(93284019437:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=5635) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C011.data C011.counts_checked C011.bounds_checked C011.weighted_checked
  have h12 : envelopePrefix F 6658 ≤ envelopePrefix F 6146+(79128713863:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=6147) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C012.data C012.counts_checked C012.bounds_checked C012.weighted_checked
  have h13 : envelopePrefix F 7170 ≤ envelopePrefix F 6658+(78710087903:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=6659) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C013.data C013.counts_checked C013.bounds_checked C013.weighted_checked
  have h14 : envelopePrefix F 7682 ≤ envelopePrefix F 7170+(73116359523:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=7171) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C014.data C014.counts_checked C014.bounds_checked C014.weighted_checked
  have h15 : envelopePrefix F 8194 ≤ envelopePrefix F 7682+(64843158905:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=7683) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C015.data C015.counts_checked C015.bounds_checked C015.weighted_checked
  have h16 : envelopePrefix F 8706 ≤ envelopePrefix F 8194+(64130002316:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=8195) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C016.data C016.counts_checked C016.bounds_checked C016.weighted_checked
  have h17 : envelopePrefix F 9218 ≤ envelopePrefix F 8706+(63615000721:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=8707) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C017.data C017.counts_checked C017.bounds_checked C017.weighted_checked
  have h18 : envelopePrefix F 9730 ≤ envelopePrefix F 9218+(59967980522:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=9219) (w:=0) (degree:=7) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C018.data C018.counts_checked C018.bounds_checked C018.weighted_checked
  have h19 : envelopePrefix F 10000 ≤ envelopePrefix F 9730+(30637079565:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=9731) (w:=0) (degree:=7) (B:=135)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C019.data C019.counts_checked C019.bounds_checked C019.weighted_checked
  have h20 : envelopePrefix F 18192 ≤ envelopePrefix F 10000+(681526691332:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=10001) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C020.data C020.counts_checked C020.bounds_checked C020.weighted_checked
  have h21 : envelopePrefix F 26384 ≤ envelopePrefix F 18192+(453863217947:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=18193) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C021.data C021.counts_checked C021.bounds_checked C021.weighted_checked
  have h22 : envelopePrefix F 34576 ≤ envelopePrefix F 26384+(349450238937:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=26385) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C022.data C022.counts_checked C022.bounds_checked C022.weighted_checked
  have h23 : envelopePrefix F 42768 ≤ envelopePrefix F 34576+(286135637372:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=34577) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C023.data C023.counts_checked C023.bounds_checked C023.weighted_checked
  have h24 : envelopePrefix F 50960 ≤ envelopePrefix F 42768+(236848521051:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=42769) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C024.data C024.counts_checked C024.bounds_checked C024.weighted_checked
  have h25 : envelopePrefix F 59152 ≤ envelopePrefix F 50960+(214635025130:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=50961) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C025.data C025.counts_checked C025.bounds_checked C025.weighted_checked
  have h26 : envelopePrefix F 67344 ≤ envelopePrefix F 59152+(184259454922:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=59153) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C026.data C026.counts_checked C026.bounds_checked C026.weighted_checked
  have h27 : envelopePrefix F 75536 ≤ envelopePrefix F 67344+(169310180123:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=67345) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C027.data C027.counts_checked C027.bounds_checked C027.weighted_checked
  have h28 : envelopePrefix F 83728 ≤ envelopePrefix F 75536+(155627720911:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=75537) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C028.data C028.counts_checked C028.bounds_checked C028.weighted_checked
  have h29 : envelopePrefix F 91920 ≤ envelopePrefix F 83728+(140228738191:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=83729) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C029.data C029.counts_checked C029.bounds_checked C029.weighted_checked
  have h30 : envelopePrefix F 100112 ≤ envelopePrefix F 91920+(133827691155:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=91921) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C030.data C030.counts_checked C030.bounds_checked C030.weighted_checked
  have h31 : envelopePrefix F 108304 ≤ envelopePrefix F 100112+(122819910907:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=100113) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C031.data C031.counts_checked C031.bounds_checked C031.weighted_checked
  have m0 : envelopePrefix F 1026 ≤ envelopePrefix F 2+(4821417368066:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 2050 ≤ envelopePrefix F 1026+(580349451524:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 3074 ≤ envelopePrefix F 2050+(368224879235:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 4098 ≤ envelopePrefix F 3074+(272992219857:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 5122 ≤ envelopePrefix F 4098+(218496299224:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 6146 ≤ envelopePrefix F 5122+(180033366615:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 7170 ≤ envelopePrefix F 6146+(157838801766:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 8194 ≤ envelopePrefix F 7170+(137959518428:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 9218 ≤ envelopePrefix F 8194+(127745003037:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 10000 ≤ envelopePrefix F 9218+(90605060087:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 26384 ≤ envelopePrefix F 10000+(1135389909279:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 42768 ≤ envelopePrefix F 26384+(635585876309:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 59152 ≤ envelopePrefix F 42768+(451483546181:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 75536 ≤ envelopePrefix F 59152+(353569635045:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 91920 ≤ envelopePrefix F 75536+(295856459102:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 108304 ≤ envelopePrefix F 91920+(256647602062:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 2050 ≤ envelopePrefix F 2+(5401766819590:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 4098 ≤ envelopePrefix F 2050+(641217099092:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 6146 ≤ envelopePrefix F 4098+(398529665839:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 8194 ≤ envelopePrefix F 6146+(295798320194:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 10000 ≤ envelopePrefix F 8194+(218350063124:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 42768 ≤ envelopePrefix F 10000+(1770975785588:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 75536 ≤ envelopePrefix F 42768+(805053181226:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 108304 ≤ envelopePrefix F 75536+(552504061164:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 4098 ≤ envelopePrefix F 2+(6042983918682:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 8194 ≤ envelopePrefix F 4098+(694327986033:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 42768 ≤ envelopePrefix F 8194+(1989325848712:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 108304 ≤ envelopePrefix F 42768+(1357557242390:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 8194 ≤ envelopePrefix F 2+(6737311904715:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 108304 ≤ envelopePrefix F 8194+(3346883091102:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 108304 ≤ envelopePrefix F 2+(10084194995817:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup00_bound
end ChenEffective.H10Band
end
