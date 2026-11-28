import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C192
import GRHQuarterCertificates.C193
import GRHQuarterCertificates.C194
import GRHQuarterCertificates.C195
import GRHQuarterCertificates.C196
import GRHQuarterCertificates.C197
import GRHQuarterCertificates.C198
import GRHQuarterCertificates.C199
import GRHQuarterCertificates.C200
import GRHQuarterCertificates.C201
import GRHQuarterCertificates.C202
import GRHQuarterCertificates.C203
import GRHQuarterCertificates.C204
import GRHQuarterCertificates.C205
import GRHQuarterCertificates.C206
import GRHQuarterCertificates.C207
import GRHQuarterCertificates.C208
import GRHQuarterCertificates.C209
import GRHQuarterCertificates.C210
import GRHQuarterCertificates.C211
import GRHQuarterCertificates.C212
import GRHQuarterCertificates.C213
import GRHQuarterCertificates.C214
import GRHQuarterCertificates.C215
import GRHQuarterCertificates.C216
import GRHQuarterCertificates.C217
import GRHQuarterCertificates.C218
import GRHQuarterCertificates.C219
import GRHQuarterCertificates.C220
import GRHQuarterCertificates.C221
import GRHQuarterCertificates.C222
import GRHQuarterCertificates.C223
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup06_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 1681168 ≤ envelopePrefix F 1419024+(424218026570:ℝ)/denominator := by
  have h0 : envelopePrefix F 1427216 ≤ envelopePrefix F 1419024+(14462023891:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1419025) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C192.data C192.counts_checked C192.bounds_checked C192.weighted_checked
  have h1 : envelopePrefix F 1435408 ≤ envelopePrefix F 1427216+(14521730847:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1427217) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C193.data C193.counts_checked C193.bounds_checked C193.weighted_checked
  have h2 : envelopePrefix F 1443600 ≤ envelopePrefix F 1435408+(14022970731:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1435409) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C194.data C194.counts_checked C194.bounds_checked C194.weighted_checked
  have h3 : envelopePrefix F 1451792 ≤ envelopePrefix F 1443600+(13963230905:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1443601) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C195.data C195.counts_checked C195.bounds_checked C195.weighted_checked
  have h4 : envelopePrefix F 1459984 ≤ envelopePrefix F 1451792+(13832640156:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1451793) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C196.data C196.counts_checked C196.bounds_checked C196.weighted_checked
  have h5 : envelopePrefix F 1468176 ≤ envelopePrefix F 1459984+(14062809704:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1459985) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C197.data C197.counts_checked C197.bounds_checked C197.weighted_checked
  have h6 : envelopePrefix F 1476368 ≤ envelopePrefix F 1468176+(13382188510:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1468177) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C198.data C198.counts_checked C198.bounds_checked C198.weighted_checked
  have h7 : envelopePrefix F 1484560 ≤ envelopePrefix F 1476368+(14373602854:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1476369) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C199.data C199.counts_checked C199.bounds_checked C199.weighted_checked
  have h8 : envelopePrefix F 1492752 ≤ envelopePrefix F 1484560+(13697049851:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1484561) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C200.data C200.counts_checked C200.bounds_checked C200.weighted_checked
  have h9 : envelopePrefix F 1500944 ≤ envelopePrefix F 1492752+(13618073984:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1492753) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C201.data C201.counts_checked C201.bounds_checked C201.weighted_checked
  have h10 : envelopePrefix F 1509136 ≤ envelopePrefix F 1500944+(13985054990:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1500945) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C202.data C202.counts_checked C202.bounds_checked C202.weighted_checked
  have h11 : envelopePrefix F 1517328 ≤ envelopePrefix F 1509136+(13413727889:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1509137) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C203.data C203.counts_checked C203.bounds_checked C203.weighted_checked
  have h12 : envelopePrefix F 1525520 ≤ envelopePrefix F 1517328+(13312470911:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1517329) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C204.data C204.counts_checked C204.bounds_checked C204.weighted_checked
  have h13 : envelopePrefix F 1533712 ≤ envelopePrefix F 1525520+(12678768017:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1525521) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C205.data C205.counts_checked C205.bounds_checked C205.weighted_checked
  have h14 : envelopePrefix F 1541904 ≤ envelopePrefix F 1533712+(13414469365:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1533713) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C206.data C206.counts_checked C206.bounds_checked C206.weighted_checked
  have h15 : envelopePrefix F 1550096 ≤ envelopePrefix F 1541904+(13107170705:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1541905) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C207.data C207.counts_checked C207.bounds_checked C207.weighted_checked
  have h16 : envelopePrefix F 1558288 ≤ envelopePrefix F 1550096+(13193535469:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1550097) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C208.data C208.counts_checked C208.bounds_checked C208.weighted_checked
  have h17 : envelopePrefix F 1566480 ≤ envelopePrefix F 1558288+(13255904468:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1558289) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C209.data C209.counts_checked C209.bounds_checked C209.weighted_checked
  have h18 : envelopePrefix F 1574672 ≤ envelopePrefix F 1566480+(13021287685:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1566481) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C210.data C210.counts_checked C210.bounds_checked C210.weighted_checked
  have h19 : envelopePrefix F 1582864 ≤ envelopePrefix F 1574672+(12540428777:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1574673) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C211.data C211.counts_checked C211.bounds_checked C211.weighted_checked
  have h20 : envelopePrefix F 1591056 ≤ envelopePrefix F 1582864+(12875809584:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1582865) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C212.data C212.counts_checked C212.bounds_checked C212.weighted_checked
  have h21 : envelopePrefix F 1599248 ≤ envelopePrefix F 1591056+(12623362309:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1591057) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C213.data C213.counts_checked C213.bounds_checked C213.weighted_checked
  have h22 : envelopePrefix F 1607440 ≤ envelopePrefix F 1599248+(13337347982:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1599249) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C214.data C214.counts_checked C214.bounds_checked C214.weighted_checked
  have h23 : envelopePrefix F 1615632 ≤ envelopePrefix F 1607440+(12393347080:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1607441) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C215.data C215.counts_checked C215.bounds_checked C215.weighted_checked
  have h24 : envelopePrefix F 1623824 ≤ envelopePrefix F 1615632+(12746857672:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1615633) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C216.data C216.counts_checked C216.bounds_checked C216.weighted_checked
  have h25 : envelopePrefix F 1632016 ≤ envelopePrefix F 1623824+(12986894372:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1623825) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C217.data C217.counts_checked C217.bounds_checked C217.weighted_checked
  have h26 : envelopePrefix F 1640208 ≤ envelopePrefix F 1632016+(12563288580:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1632017) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C218.data C218.counts_checked C218.bounds_checked C218.weighted_checked
  have h27 : envelopePrefix F 1648400 ≤ envelopePrefix F 1640208+(12405352126:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1640209) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C219.data C219.counts_checked C219.bounds_checked C219.weighted_checked
  have h28 : envelopePrefix F 1656592 ≤ envelopePrefix F 1648400+(12819278156:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1648401) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C220.data C220.counts_checked C220.bounds_checked C220.weighted_checked
  have h29 : envelopePrefix F 1664784 ≤ envelopePrefix F 1656592+(11942744721:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1656593) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C221.data C221.counts_checked C221.bounds_checked C221.weighted_checked
  have h30 : envelopePrefix F 1672976 ≤ envelopePrefix F 1664784+(12834546270:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1664785) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C222.data C222.counts_checked C222.bounds_checked C222.weighted_checked
  have h31 : envelopePrefix F 1681168 ≤ envelopePrefix F 1672976+(12830058009:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1672977) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C223.data C223.counts_checked C223.bounds_checked C223.weighted_checked
  have m0 : envelopePrefix F 1435408 ≤ envelopePrefix F 1419024+(28983754738:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 1451792 ≤ envelopePrefix F 1435408+(27986201636:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 1468176 ≤ envelopePrefix F 1451792+(27895449860:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 1484560 ≤ envelopePrefix F 1468176+(27755791364:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 1500944 ≤ envelopePrefix F 1484560+(27315123835:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 1517328 ≤ envelopePrefix F 1500944+(27398782879:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 1533712 ≤ envelopePrefix F 1517328+(25991238928:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 1550096 ≤ envelopePrefix F 1533712+(26521640070:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 1566480 ≤ envelopePrefix F 1550096+(26449439937:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 1582864 ≤ envelopePrefix F 1566480+(25561716462:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 1599248 ≤ envelopePrefix F 1582864+(25499171893:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 1615632 ≤ envelopePrefix F 1599248+(25730695062:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 1632016 ≤ envelopePrefix F 1615632+(25733752044:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 1648400 ≤ envelopePrefix F 1632016+(24968640706:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 1664784 ≤ envelopePrefix F 1648400+(24762022877:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 1681168 ≤ envelopePrefix F 1664784+(25664604279:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 1451792 ≤ envelopePrefix F 1419024+(56969956374:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 1484560 ≤ envelopePrefix F 1451792+(55651241224:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 1517328 ≤ envelopePrefix F 1484560+(54713906714:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 1550096 ≤ envelopePrefix F 1517328+(52512878998:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 1582864 ≤ envelopePrefix F 1550096+(52011156399:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 1615632 ≤ envelopePrefix F 1582864+(51229866955:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 1648400 ≤ envelopePrefix F 1615632+(50702392750:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 1681168 ≤ envelopePrefix F 1648400+(50426627156:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 1484560 ≤ envelopePrefix F 1419024+(112621197598:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 1550096 ≤ envelopePrefix F 1484560+(107226785712:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 1615632 ≤ envelopePrefix F 1550096+(103241023354:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 1681168 ≤ envelopePrefix F 1615632+(101129019906:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 1550096 ≤ envelopePrefix F 1419024+(219847983310:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 1681168 ≤ envelopePrefix F 1550096+(204370043260:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 1681168 ≤ envelopePrefix F 1419024+(424218026570:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup06_bound
end ChenEffective.H10Band
end
