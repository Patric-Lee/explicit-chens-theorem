import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C224
import GRHQuarterCertificates.C225
import GRHQuarterCertificates.C226
import GRHQuarterCertificates.C227
import GRHQuarterCertificates.C228
import GRHQuarterCertificates.C229
import GRHQuarterCertificates.C230
import GRHQuarterCertificates.C231
import GRHQuarterCertificates.C232
import GRHQuarterCertificates.C233
import GRHQuarterCertificates.C234
import GRHQuarterCertificates.C235
import GRHQuarterCertificates.C236
import GRHQuarterCertificates.C237
import GRHQuarterCertificates.C238
import GRHQuarterCertificates.C239
import GRHQuarterCertificates.C240
import GRHQuarterCertificates.C241
import GRHQuarterCertificates.C242
import GRHQuarterCertificates.C243
import GRHQuarterCertificates.C244
import GRHQuarterCertificates.C245
import GRHQuarterCertificates.C246
import GRHQuarterCertificates.C247
import GRHQuarterCertificates.C248
import GRHQuarterCertificates.C249
import GRHQuarterCertificates.C250
import GRHQuarterCertificates.C251
import GRHQuarterCertificates.C252
import GRHQuarterCertificates.C253
import GRHQuarterCertificates.C254
import GRHQuarterCertificates.C255
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup07_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 1943312 ≤ envelopePrefix F 1681168+(372660719996:ℝ)/denominator := by
  have h0 : envelopePrefix F 1689360 ≤ envelopePrefix F 1681168+(11897816192:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1681169) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C224.data C224.counts_checked C224.bounds_checked C224.weighted_checked
  have h1 : envelopePrefix F 1697552 ≤ envelopePrefix F 1689360+(12327891085:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1689361) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C225.data C225.counts_checked C225.bounds_checked C225.weighted_checked
  have h2 : envelopePrefix F 1705744 ≤ envelopePrefix F 1697552+(12305581613:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1697553) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C226.data C226.counts_checked C226.bounds_checked C226.weighted_checked
  have h3 : envelopePrefix F 1713936 ≤ envelopePrefix F 1705744+(12090285977:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1705745) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C227.data C227.counts_checked C227.bounds_checked C227.weighted_checked
  have h4 : envelopePrefix F 1722128 ≤ envelopePrefix F 1713936+(12174335441:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1713937) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C228.data C228.counts_checked C228.bounds_checked C228.weighted_checked
  have h5 : envelopePrefix F 1730320 ≤ envelopePrefix F 1722128+(11897319598:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1722129) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C229.data C229.counts_checked C229.bounds_checked C229.weighted_checked
  have h6 : envelopePrefix F 1738512 ≤ envelopePrefix F 1730320+(11686384634:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1730321) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C230.data C230.counts_checked C230.bounds_checked C230.weighted_checked
  have h7 : envelopePrefix F 1746704 ≤ envelopePrefix F 1738512+(12150759718:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1738513) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C231.data C231.counts_checked C231.bounds_checked C231.weighted_checked
  have h8 : envelopePrefix F 1754896 ≤ envelopePrefix F 1746704+(12506815319:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1746705) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C232.data C232.counts_checked C232.bounds_checked C232.weighted_checked
  have h9 : envelopePrefix F 1763088 ≤ envelopePrefix F 1754896+(10999367303:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1754897) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C233.data C233.counts_checked C233.bounds_checked C233.weighted_checked
  have h10 : envelopePrefix F 1771280 ≤ envelopePrefix F 1763088+(12023695865:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1763089) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C234.data C234.counts_checked C234.bounds_checked C234.weighted_checked
  have h11 : envelopePrefix F 1779472 ≤ envelopePrefix F 1771280+(11960893887:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1771281) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C235.data C235.counts_checked C235.bounds_checked C235.weighted_checked
  have h12 : envelopePrefix F 1787664 ≤ envelopePrefix F 1779472+(11899267036:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1779473) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C236.data C236.counts_checked C236.bounds_checked C236.weighted_checked
  have h13 : envelopePrefix F 1795856 ≤ envelopePrefix F 1787664+(11734146879:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1787665) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C237.data C237.counts_checked C237.bounds_checked C237.weighted_checked
  have h14 : envelopePrefix F 1804048 ≤ envelopePrefix F 1795856+(11550915195:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1795857) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C238.data C238.counts_checked C238.bounds_checked C238.weighted_checked
  have h15 : envelopePrefix F 1812240 ≤ envelopePrefix F 1804048+(11941851792:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1804049) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C239.data C239.counts_checked C239.bounds_checked C239.weighted_checked
  have h16 : envelopePrefix F 1820432 ≤ envelopePrefix F 1812240+(11288958964:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1812241) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C240.data C240.counts_checked C240.bounds_checked C240.weighted_checked
  have h17 : envelopePrefix F 1828624 ≤ envelopePrefix F 1820432+(12003460430:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1820433) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C241.data C241.counts_checked C241.bounds_checked C241.weighted_checked
  have h18 : envelopePrefix F 1836816 ≤ envelopePrefix F 1828624+(11375854304:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1828625) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C242.data C242.counts_checked C242.bounds_checked C242.weighted_checked
  have h19 : envelopePrefix F 1845008 ≤ envelopePrefix F 1836816+(11357030339:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1836817) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C243.data C243.counts_checked C243.bounds_checked C243.weighted_checked
  have h20 : envelopePrefix F 1853200 ≤ envelopePrefix F 1845008+(11420548611:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1845009) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C244.data C244.counts_checked C244.bounds_checked C244.weighted_checked
  have h21 : envelopePrefix F 1861392 ≤ envelopePrefix F 1853200+(11764419327:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1853201) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C245.data C245.counts_checked C245.bounds_checked C245.weighted_checked
  have h22 : envelopePrefix F 1869584 ≤ envelopePrefix F 1861392+(11705203707:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1861393) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C246.data C246.counts_checked C246.bounds_checked C246.weighted_checked
  have h23 : envelopePrefix F 1877776 ≤ envelopePrefix F 1869584+(11167986801:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1869585) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C247.data C247.counts_checked C247.bounds_checked C247.weighted_checked
  have h24 : envelopePrefix F 1885968 ≤ envelopePrefix F 1877776+(11270942656:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1877777) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C248.data C248.counts_checked C248.bounds_checked C248.weighted_checked
  have h25 : envelopePrefix F 1894160 ≤ envelopePrefix F 1885968+(11511522008:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1885969) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C249.data C249.counts_checked C249.bounds_checked C249.weighted_checked
  have h26 : envelopePrefix F 1902352 ≤ envelopePrefix F 1894160+(10822676912:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1894161) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C250.data C250.counts_checked C250.bounds_checked C250.weighted_checked
  have h27 : envelopePrefix F 1910544 ≤ envelopePrefix F 1902352+(11181211238:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1902353) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C251.data C251.counts_checked C251.bounds_checked C251.weighted_checked
  have h28 : envelopePrefix F 1918736 ≤ envelopePrefix F 1910544+(11439975742:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1910545) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C252.data C252.counts_checked C252.bounds_checked C252.weighted_checked
  have h29 : envelopePrefix F 1926928 ≤ envelopePrefix F 1918736+(11011615128:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1918737) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C253.data C253.counts_checked C253.bounds_checked C253.weighted_checked
  have h30 : envelopePrefix F 1935120 ≤ envelopePrefix F 1926928+(11055495731:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1926929) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C254.data C254.counts_checked C254.bounds_checked C254.weighted_checked
  have h31 : envelopePrefix F 1943312 ≤ envelopePrefix F 1935120+(11136490564:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1935121) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C255.data C255.counts_checked C255.bounds_checked C255.weighted_checked
  have m0 : envelopePrefix F 1697552 ≤ envelopePrefix F 1681168+(24225707277:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 1713936 ≤ envelopePrefix F 1697552+(24395867590:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 1730320 ≤ envelopePrefix F 1713936+(24071655039:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 1746704 ≤ envelopePrefix F 1730320+(23837144352:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 1763088 ≤ envelopePrefix F 1746704+(23506182622:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 1779472 ≤ envelopePrefix F 1763088+(23984589752:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 1795856 ≤ envelopePrefix F 1779472+(23633413915:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 1812240 ≤ envelopePrefix F 1795856+(23492766987:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 1828624 ≤ envelopePrefix F 1812240+(23292419394:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 1845008 ≤ envelopePrefix F 1828624+(22732884643:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 1861392 ≤ envelopePrefix F 1845008+(23184967938:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 1877776 ≤ envelopePrefix F 1861392+(22873190508:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 1894160 ≤ envelopePrefix F 1877776+(22782464664:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 1910544 ≤ envelopePrefix F 1894160+(22003888150:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 1926928 ≤ envelopePrefix F 1910544+(22451590870:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 1943312 ≤ envelopePrefix F 1926928+(22191986295:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 1713936 ≤ envelopePrefix F 1681168+(48621574867:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 1746704 ≤ envelopePrefix F 1713936+(47908799391:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 1779472 ≤ envelopePrefix F 1746704+(47490772374:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 1812240 ≤ envelopePrefix F 1779472+(47126180902:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 1845008 ≤ envelopePrefix F 1812240+(46025304037:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 1877776 ≤ envelopePrefix F 1845008+(46058158446:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 1910544 ≤ envelopePrefix F 1877776+(44786352814:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 1943312 ≤ envelopePrefix F 1910544+(44643577165:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 1746704 ≤ envelopePrefix F 1681168+(96530374258:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 1812240 ≤ envelopePrefix F 1746704+(94616953276:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 1877776 ≤ envelopePrefix F 1812240+(92083462483:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 1943312 ≤ envelopePrefix F 1877776+(89429929979:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 1812240 ≤ envelopePrefix F 1681168+(191147327534:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 1943312 ≤ envelopePrefix F 1812240+(181513392462:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 1943312 ≤ envelopePrefix F 1681168+(372660719996:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup07_bound
end ChenEffective.H10Band
end
