import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C128
import GRHQuarterCertificates.C129
import GRHQuarterCertificates.C130
import GRHQuarterCertificates.C131
import GRHQuarterCertificates.C132
import GRHQuarterCertificates.C133
import GRHQuarterCertificates.C134
import GRHQuarterCertificates.C135
import GRHQuarterCertificates.C136
import GRHQuarterCertificates.C137
import GRHQuarterCertificates.C138
import GRHQuarterCertificates.C139
import GRHQuarterCertificates.C140
import GRHQuarterCertificates.C141
import GRHQuarterCertificates.C142
import GRHQuarterCertificates.C143
import GRHQuarterCertificates.C144
import GRHQuarterCertificates.C145
import GRHQuarterCertificates.C146
import GRHQuarterCertificates.C147
import GRHQuarterCertificates.C148
import GRHQuarterCertificates.C149
import GRHQuarterCertificates.C150
import GRHQuarterCertificates.C151
import GRHQuarterCertificates.C152
import GRHQuarterCertificates.C153
import GRHQuarterCertificates.C154
import GRHQuarterCertificates.C155
import GRHQuarterCertificates.C156
import GRHQuarterCertificates.C157
import GRHQuarterCertificates.C158
import GRHQuarterCertificates.C159
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup04_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 1156880 ≤ envelopePrefix F 894736+(594486203357:ℝ)/denominator := by
  have h0 : envelopePrefix F 902928 ≤ envelopePrefix F 894736+(20067814768:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=894737) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C128.data C128.counts_checked C128.bounds_checked C128.weighted_checked
  have h1 : envelopePrefix F 911120 ≤ envelopePrefix F 902928+(21133631433:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=902929) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C129.data C129.counts_checked C129.bounds_checked C129.weighted_checked
  have h2 : envelopePrefix F 919312 ≤ envelopePrefix F 911120+(20035324226:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=911121) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C130.data C130.counts_checked C130.bounds_checked C130.weighted_checked
  have h3 : envelopePrefix F 927504 ≤ envelopePrefix F 919312+(20513009156:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=919313) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C131.data C131.counts_checked C131.bounds_checked C131.weighted_checked
  have h4 : envelopePrefix F 935696 ≤ envelopePrefix F 927504+(20073830088:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=927505) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C132.data C132.counts_checked C132.bounds_checked C132.weighted_checked
  have h5 : envelopePrefix F 943888 ≤ envelopePrefix F 935696+(19908164668:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=935697) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C133.data C133.counts_checked C133.bounds_checked C133.weighted_checked
  have h6 : envelopePrefix F 952080 ≤ envelopePrefix F 943888+(19148040352:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=943889) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C134.data C134.counts_checked C134.bounds_checked C134.weighted_checked
  have h7 : envelopePrefix F 960272 ≤ envelopePrefix F 952080+(19158081456:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=952081) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C135.data C135.counts_checked C135.bounds_checked C135.weighted_checked
  have h8 : envelopePrefix F 968464 ≤ envelopePrefix F 960272+(19791034653:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=960273) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C136.data C136.counts_checked C136.bounds_checked C136.weighted_checked
  have h9 : envelopePrefix F 976656 ≤ envelopePrefix F 968464+(19665208336:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=968465) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C137.data C137.counts_checked C137.bounds_checked C137.weighted_checked
  have h10 : envelopePrefix F 984848 ≤ envelopePrefix F 976656+(18277305470:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=976657) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C138.data C138.counts_checked C138.bounds_checked C138.weighted_checked
  have h11 : envelopePrefix F 993040 ≤ envelopePrefix F 984848+(18905457317:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=984849) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C139.data C139.counts_checked C139.bounds_checked C139.weighted_checked
  have h12 : envelopePrefix F 1001232 ≤ envelopePrefix F 993040+(19108336579:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=993041) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C140.data C140.counts_checked C140.bounds_checked C140.weighted_checked
  have h13 : envelopePrefix F 1009424 ≤ envelopePrefix F 1001232+(19659200215:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1001233) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C141.data C141.counts_checked C141.bounds_checked C141.weighted_checked
  have h14 : envelopePrefix F 1017616 ≤ envelopePrefix F 1009424+(18654661331:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1009425) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C142.data C142.counts_checked C142.bounds_checked C142.weighted_checked
  have h15 : envelopePrefix F 1025808 ≤ envelopePrefix F 1017616+(18888140617:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1017617) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C143.data C143.counts_checked C143.bounds_checked C143.weighted_checked
  have h16 : envelopePrefix F 1034000 ≤ envelopePrefix F 1025808+(18150989822:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1025809) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C144.data C144.counts_checked C144.bounds_checked C144.weighted_checked
  have h17 : envelopePrefix F 1042192 ≤ envelopePrefix F 1034000+(18260826943:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1034001) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C145.data C145.counts_checked C145.bounds_checked C145.weighted_checked
  have h18 : envelopePrefix F 1050384 ≤ envelopePrefix F 1042192+(18215031547:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1042193) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C146.data C146.counts_checked C146.bounds_checked C146.weighted_checked
  have h19 : envelopePrefix F 1058576 ≤ envelopePrefix F 1050384+(17433151689:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1050385) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C147.data C147.counts_checked C147.bounds_checked C147.weighted_checked
  have h20 : envelopePrefix F 1066768 ≤ envelopePrefix F 1058576+(17729754729:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1058577) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C148.data C148.counts_checked C148.bounds_checked C148.weighted_checked
  have h21 : envelopePrefix F 1074960 ≤ envelopePrefix F 1066768+(17931680523:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1066769) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C149.data C149.counts_checked C149.bounds_checked C149.weighted_checked
  have h22 : envelopePrefix F 1083152 ≤ envelopePrefix F 1074960+(18191448432:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1074961) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C150.data C150.counts_checked C150.bounds_checked C150.weighted_checked
  have h23 : envelopePrefix F 1091344 ≤ envelopePrefix F 1083152+(17367768892:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1083153) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C151.data C151.counts_checked C151.bounds_checked C151.weighted_checked
  have h24 : envelopePrefix F 1099536 ≤ envelopePrefix F 1091344+(17808751301:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1091345) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C152.data C152.counts_checked C152.bounds_checked C152.weighted_checked
  have h25 : envelopePrefix F 1107728 ≤ envelopePrefix F 1099536+(17767882150:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1099537) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C153.data C153.counts_checked C153.bounds_checked C153.weighted_checked
  have h26 : envelopePrefix F 1115920 ≤ envelopePrefix F 1107728+(18053320327:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1107729) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C154.data C154.counts_checked C154.bounds_checked C154.weighted_checked
  have h27 : envelopePrefix F 1124112 ≤ envelopePrefix F 1115920+(16662740969:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1115921) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C155.data C155.counts_checked C155.bounds_checked C155.weighted_checked
  have h28 : envelopePrefix F 1132304 ≤ envelopePrefix F 1124112+(17213774498:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1124113) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C156.data C156.counts_checked C156.bounds_checked C156.weighted_checked
  have h29 : envelopePrefix F 1140496 ≤ envelopePrefix F 1132304+(17063684275:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1132305) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C157.data C157.counts_checked C157.bounds_checked C157.weighted_checked
  have h30 : envelopePrefix F 1148688 ≤ envelopePrefix F 1140496+(16451872095:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1140497) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C158.data C158.counts_checked C158.bounds_checked C158.weighted_checked
  have h31 : envelopePrefix F 1156880 ≤ envelopePrefix F 1148688+(17196284500:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1148689) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C159.data C159.counts_checked C159.bounds_checked C159.weighted_checked
  have m0 : envelopePrefix F 911120 ≤ envelopePrefix F 894736+(41201446201:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 927504 ≤ envelopePrefix F 911120+(40548333382:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 943888 ≤ envelopePrefix F 927504+(39981994756:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 960272 ≤ envelopePrefix F 943888+(38306121808:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 976656 ≤ envelopePrefix F 960272+(39456242989:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 993040 ≤ envelopePrefix F 976656+(37182762787:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 1009424 ≤ envelopePrefix F 993040+(38767536794:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 1025808 ≤ envelopePrefix F 1009424+(37542801948:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 1042192 ≤ envelopePrefix F 1025808+(36411816765:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 1058576 ≤ envelopePrefix F 1042192+(35648183236:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 1074960 ≤ envelopePrefix F 1058576+(35661435252:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 1091344 ≤ envelopePrefix F 1074960+(35559217324:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 1107728 ≤ envelopePrefix F 1091344+(35576633451:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 1124112 ≤ envelopePrefix F 1107728+(34716061296:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 1140496 ≤ envelopePrefix F 1124112+(34277458773:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 1156880 ≤ envelopePrefix F 1140496+(33648156595:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 927504 ≤ envelopePrefix F 894736+(81749779583:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 960272 ≤ envelopePrefix F 927504+(78288116564:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 993040 ≤ envelopePrefix F 960272+(76639005776:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 1025808 ≤ envelopePrefix F 993040+(76310338742:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 1058576 ≤ envelopePrefix F 1025808+(72060000001:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 1091344 ≤ envelopePrefix F 1058576+(71220652576:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 1124112 ≤ envelopePrefix F 1091344+(70292694747:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 1156880 ≤ envelopePrefix F 1124112+(67925615368:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 960272 ≤ envelopePrefix F 894736+(160037896147:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 1025808 ≤ envelopePrefix F 960272+(152949344518:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 1091344 ≤ envelopePrefix F 1025808+(143280652577:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 1156880 ≤ envelopePrefix F 1091344+(138218310115:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 1025808 ≤ envelopePrefix F 894736+(312987240665:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 1156880 ≤ envelopePrefix F 1025808+(281498962692:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 1156880 ≤ envelopePrefix F 894736+(594486203357:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup04_bound
end ChenEffective.H10Band
end
