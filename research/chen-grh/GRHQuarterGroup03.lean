import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C096
import GRHQuarterCertificates.C097
import GRHQuarterCertificates.C098
import GRHQuarterCertificates.C099
import GRHQuarterCertificates.C100
import GRHQuarterCertificates.C101
import GRHQuarterCertificates.C102
import GRHQuarterCertificates.C103
import GRHQuarterCertificates.C104
import GRHQuarterCertificates.C105
import GRHQuarterCertificates.C106
import GRHQuarterCertificates.C107
import GRHQuarterCertificates.C108
import GRHQuarterCertificates.C109
import GRHQuarterCertificates.C110
import GRHQuarterCertificates.C111
import GRHQuarterCertificates.C112
import GRHQuarterCertificates.C113
import GRHQuarterCertificates.C114
import GRHQuarterCertificates.C115
import GRHQuarterCertificates.C116
import GRHQuarterCertificates.C117
import GRHQuarterCertificates.C118
import GRHQuarterCertificates.C119
import GRHQuarterCertificates.C120
import GRHQuarterCertificates.C121
import GRHQuarterCertificates.C122
import GRHQuarterCertificates.C123
import GRHQuarterCertificates.C124
import GRHQuarterCertificates.C125
import GRHQuarterCertificates.C126
import GRHQuarterCertificates.C127
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup03_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 894736 ≤ envelopePrefix F 632592+(762468839750:ℝ)/denominator := by
  have h0 : envelopePrefix F 640784 ≤ envelopePrefix F 632592+(26753747779:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=632593) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C096.data C096.counts_checked C096.bounds_checked C096.weighted_checked
  have h1 : envelopePrefix F 648976 ≤ envelopePrefix F 640784+(27205012374:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=640785) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C097.data C097.counts_checked C097.bounds_checked C097.weighted_checked
  have h2 : envelopePrefix F 657168 ≤ envelopePrefix F 648976+(26774681198:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=648977) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C098.data C098.counts_checked C098.bounds_checked C098.weighted_checked
  have h3 : envelopePrefix F 665360 ≤ envelopePrefix F 657168+(27133052245:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=657169) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C099.data C099.counts_checked C099.bounds_checked C099.weighted_checked
  have h4 : envelopePrefix F 673552 ≤ envelopePrefix F 665360+(26105761119:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=665361) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C100.data C100.counts_checked C100.bounds_checked C100.weighted_checked
  have h5 : envelopePrefix F 681744 ≤ envelopePrefix F 673552+(26211165162:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=673553) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C101.data C101.counts_checked C101.bounds_checked C101.weighted_checked
  have h6 : envelopePrefix F 689936 ≤ envelopePrefix F 681744+(25976848301:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=681745) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C102.data C102.counts_checked C102.bounds_checked C102.weighted_checked
  have h7 : envelopePrefix F 698128 ≤ envelopePrefix F 689936+(25536331414:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=689937) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C103.data C103.counts_checked C103.bounds_checked C103.weighted_checked
  have h8 : envelopePrefix F 706320 ≤ envelopePrefix F 698128+(25394557360:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=698129) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C104.data C104.counts_checked C104.bounds_checked C104.weighted_checked
  have h9 : envelopePrefix F 714512 ≤ envelopePrefix F 706320+(25014460183:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=706321) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C105.data C105.counts_checked C105.bounds_checked C105.weighted_checked
  have h10 : envelopePrefix F 722704 ≤ envelopePrefix F 714512+(24716419833:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=714513) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C106.data C106.counts_checked C106.bounds_checked C106.weighted_checked
  have h11 : envelopePrefix F 730896 ≤ envelopePrefix F 722704+(24873920284:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=722705) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C107.data C107.counts_checked C107.bounds_checked C107.weighted_checked
  have h12 : envelopePrefix F 739088 ≤ envelopePrefix F 730896+(24463474140:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=730897) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C108.data C108.counts_checked C108.bounds_checked C108.weighted_checked
  have h13 : envelopePrefix F 747280 ≤ envelopePrefix F 739088+(22986014037:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=739089) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C109.data C109.counts_checked C109.bounds_checked C109.weighted_checked
  have h14 : envelopePrefix F 755472 ≤ envelopePrefix F 747280+(24536179602:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=747281) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C110.data C110.counts_checked C110.bounds_checked C110.weighted_checked
  have h15 : envelopePrefix F 763664 ≤ envelopePrefix F 755472+(23629178226:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=755473) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C111.data C111.counts_checked C111.bounds_checked C111.weighted_checked
  have h16 : envelopePrefix F 771856 ≤ envelopePrefix F 763664+(24026971466:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=763665) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C112.data C112.counts_checked C112.bounds_checked C112.weighted_checked
  have h17 : envelopePrefix F 780048 ≤ envelopePrefix F 771856+(23139848030:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=771857) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C113.data C113.counts_checked C113.bounds_checked C113.weighted_checked
  have h18 : envelopePrefix F 788240 ≤ envelopePrefix F 780048+(23227291390:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=780049) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C114.data C114.counts_checked C114.bounds_checked C114.weighted_checked
  have h19 : envelopePrefix F 796432 ≤ envelopePrefix F 788240+(23275045330:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=788241) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C115.data C115.counts_checked C115.bounds_checked C115.weighted_checked
  have h20 : envelopePrefix F 804624 ≤ envelopePrefix F 796432+(22681885770:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=796433) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C116.data C116.counts_checked C116.bounds_checked C116.weighted_checked
  have h21 : envelopePrefix F 812816 ≤ envelopePrefix F 804624+(22620631767:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=804625) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C117.data C117.counts_checked C117.bounds_checked C117.weighted_checked
  have h22 : envelopePrefix F 821008 ≤ envelopePrefix F 812816+(22189158140:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=812817) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C118.data C118.counts_checked C118.bounds_checked C118.weighted_checked
  have h23 : envelopePrefix F 829200 ≤ envelopePrefix F 821008+(22727037097:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=821009) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C119.data C119.counts_checked C119.bounds_checked C119.weighted_checked
  have h24 : envelopePrefix F 837392 ≤ envelopePrefix F 829200+(21789692109:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=829201) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C120.data C120.counts_checked C120.bounds_checked C120.weighted_checked
  have h25 : envelopePrefix F 845584 ≤ envelopePrefix F 837392+(21629305966:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=837393) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C121.data C121.counts_checked C121.bounds_checked C121.weighted_checked
  have h26 : envelopePrefix F 853776 ≤ envelopePrefix F 845584+(21221176797:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=845585) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C122.data C122.counts_checked C122.bounds_checked C122.weighted_checked
  have h27 : envelopePrefix F 861968 ≤ envelopePrefix F 853776+(21641668845:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=853777) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C123.data C123.counts_checked C123.bounds_checked C123.weighted_checked
  have h28 : envelopePrefix F 870160 ≤ envelopePrefix F 861968+(21985984283:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=861969) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C124.data C124.counts_checked C124.bounds_checked C124.weighted_checked
  have h29 : envelopePrefix F 878352 ≤ envelopePrefix F 870160+(20841637191:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=870161) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C125.data C125.counts_checked C125.bounds_checked C125.weighted_checked
  have h30 : envelopePrefix F 886544 ≤ envelopePrefix F 878352+(21328788592:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=878353) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C126.data C126.counts_checked C126.bounds_checked C126.weighted_checked
  have h31 : envelopePrefix F 894736 ≤ envelopePrefix F 886544+(20831913720:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=886545) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C127.data C127.counts_checked C127.bounds_checked C127.weighted_checked
  have m0 : envelopePrefix F 648976 ≤ envelopePrefix F 632592+(53958760153:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 665360 ≤ envelopePrefix F 648976+(53907733443:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 681744 ≤ envelopePrefix F 665360+(52316926281:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 698128 ≤ envelopePrefix F 681744+(51513179715:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 714512 ≤ envelopePrefix F 698128+(50409017543:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 730896 ≤ envelopePrefix F 714512+(49590340117:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 747280 ≤ envelopePrefix F 730896+(47449488177:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 763664 ≤ envelopePrefix F 747280+(48165357828:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 780048 ≤ envelopePrefix F 763664+(47166819496:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 796432 ≤ envelopePrefix F 780048+(46502336720:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 812816 ≤ envelopePrefix F 796432+(45302517537:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 829200 ≤ envelopePrefix F 812816+(44916195237:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 845584 ≤ envelopePrefix F 829200+(43418998075:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 861968 ≤ envelopePrefix F 845584+(42862845642:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 878352 ≤ envelopePrefix F 861968+(42827621474:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 894736 ≤ envelopePrefix F 878352+(42160702312:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 665360 ≤ envelopePrefix F 632592+(107866493596:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 698128 ≤ envelopePrefix F 665360+(103830105996:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 730896 ≤ envelopePrefix F 698128+(99999357660:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 763664 ≤ envelopePrefix F 730896+(95614846005:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 796432 ≤ envelopePrefix F 763664+(93669156216:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 829200 ≤ envelopePrefix F 796432+(90218712774:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 861968 ≤ envelopePrefix F 829200+(86281843717:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 894736 ≤ envelopePrefix F 861968+(84988323786:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 698128 ≤ envelopePrefix F 632592+(211696599592:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 763664 ≤ envelopePrefix F 698128+(195614203665:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 829200 ≤ envelopePrefix F 763664+(183887868990:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 894736 ≤ envelopePrefix F 829200+(171270167503:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 763664 ≤ envelopePrefix F 632592+(407310803257:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 894736 ≤ envelopePrefix F 763664+(355158036493:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 894736 ≤ envelopePrefix F 632592+(762468839750:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup03_bound
end ChenEffective.H10Band
end
