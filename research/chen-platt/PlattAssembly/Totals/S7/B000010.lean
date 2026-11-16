import PlattSegmentPacket
import PlattCertificates.Count131072.C060320
import PlattCertificates.Count131072.C060321
import PlattCertificates.Count131072.C060322
import PlattCertificates.Count131072.C060323
import PlattCertificates.Count131072.C060324
import PlattCertificates.Count131072.C060325
import PlattCertificates.Count131072.C060326
import PlattCertificates.Count131072.C060327
import PlattCertificates.Count131072.C060328
import PlattCertificates.Count131072.C060329
import PlattCertificates.Count131072.C060330
import PlattCertificates.Count131072.C060331
import PlattCertificates.Count131072.C060332
import PlattCertificates.Count131072.C060333
import PlattCertificates.Count131072.C060334
import PlattCertificates.Count131072.C060335
import PlattCertificates.Count131072.C060336
import PlattCertificates.Count131072.C060337
import PlattCertificates.Count131072.C060338
import PlattCertificates.Count131072.C060339
import PlattCertificates.Count131072.C060340
import PlattCertificates.Count131072.C060341
import PlattCertificates.Count131072.C060342
import PlattCertificates.Count131072.C060343
import PlattCertificates.Count131072.C060344
import PlattCertificates.Count131072.C060345
import PlattCertificates.Count131072.C060346
import PlattCertificates.Count131072.C060347
import PlattCertificates.Count131072.C060348
import PlattCertificates.Count131072.C060349
import PlattCertificates.Count131072.C060350
import PlattCertificates.Count131072.C060351
namespace ChenEffective.PlattWindow.Assembly.Totals.S7.B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨7910195200,7910326272,210440907,210441029⟩
opaque packet0 : SegmentPacket 7910195201 10 64 210440907 210441029 := ⟨Manual.Count131072.C060320.packed,Manual.Count131072.C060320.count_checked,Manual.Count131072.C060320.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 7910195201 10 64 packet0.packed 210440907 210441029
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨7910326272,7910457344,203534347,203534464⟩
opaque packet1 : SegmentPacket 7910326273 10 64 203534347 203534464 := ⟨Manual.Count131072.C060321.packed,Manual.Count131072.C060321.count_checked,Manual.Count131072.C060321.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 7910326273 10 64 packet1.packed 203534347 203534464
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨7910457344,7910588416,205310099,205310212⟩
opaque packet2 : SegmentPacket 7910457345 10 64 205310099 205310212 := ⟨Manual.Count131072.C060322.packed,Manual.Count131072.C060322.count_checked,Manual.Count131072.C060322.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 7910457345 10 64 packet2.packed 205310099 205310212
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨7910588416,7910719488,206231812,206231931⟩
opaque packet3 : SegmentPacket 7910588417 10 64 206231812 206231931 := ⟨Manual.Count131072.C060323.packed,Manual.Count131072.C060323.count_checked,Manual.Count131072.C060323.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 7910588417 10 64 packet3.packed 206231812 206231931
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨7910719488,7910850560,203880030,203880143⟩
opaque packet4 : SegmentPacket 7910719489 10 64 203880030 203880143 := ⟨Manual.Count131072.C060324.packed,Manual.Count131072.C060324.count_checked,Manual.Count131072.C060324.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 7910719489 10 64 packet4.packed 203880030 203880143
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨7910850560,7910981632,203200635,203200752⟩
opaque packet5 : SegmentPacket 7910850561 10 64 203200635 203200752 := ⟨Manual.Count131072.C060325.packed,Manual.Count131072.C060325.count_checked,Manual.Count131072.C060325.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 7910850561 10 64 packet5.packed 203200635 203200752
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨7910981632,7911112704,203232856,203232974⟩
opaque packet6 : SegmentPacket 7910981633 10 64 203232856 203232974 := ⟨Manual.Count131072.C060326.packed,Manual.Count131072.C060326.count_checked,Manual.Count131072.C060326.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 7910981633 10 64 packet6.packed 203232856 203232974
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨7911112704,7911243776,200134065,200134182⟩
opaque packet7 : SegmentPacket 7911112705 10 64 200134065 200134182 := ⟨Manual.Count131072.C060327.packed,Manual.Count131072.C060327.count_checked,Manual.Count131072.C060327.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 7911112705 10 64 packet7.packed 200134065 200134182
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def row8 : IncrementRow := ⟨7911243776,7911374848,204542507,204542625⟩
opaque packet8 : SegmentPacket 7911243777 10 64 204542507 204542625 := ⟨Manual.Count131072.C060328.packed,Manual.Count131072.C060328.count_checked,Manual.Count131072.C060328.arithmetic_checked⟩
theorem certified8 : IncrementCertified row8 := certifyIncrement 7911243777 10 64 packet8.packed 204542507 204542625
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet8.counts packet8.arithmetic
def row9 : IncrementRow := ⟨7911374848,7911505920,206353625,206353743⟩
opaque packet9 : SegmentPacket 7911374849 10 64 206353625 206353743 := ⟨Manual.Count131072.C060329.packed,Manual.Count131072.C060329.count_checked,Manual.Count131072.C060329.arithmetic_checked⟩
theorem certified9 : IncrementCertified row9 := certifyIncrement 7911374849 10 64 packet9.packed 206353625 206353743
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet9.counts packet9.arithmetic
def row10 : IncrementRow := ⟨7911505920,7911636992,203468433,203468547⟩
opaque packet10 : SegmentPacket 7911505921 10 64 203468433 203468547 := ⟨Manual.Count131072.C060330.packed,Manual.Count131072.C060330.count_checked,Manual.Count131072.C060330.arithmetic_checked⟩
theorem certified10 : IncrementCertified row10 := certifyIncrement 7911505921 10 64 packet10.packed 203468433 203468547
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet10.counts packet10.arithmetic
def row11 : IncrementRow := ⟨7911636992,7911768064,204745820,204745935⟩
opaque packet11 : SegmentPacket 7911636993 10 64 204745820 204745935 := ⟨Manual.Count131072.C060331.packed,Manual.Count131072.C060331.count_checked,Manual.Count131072.C060331.arithmetic_checked⟩
theorem certified11 : IncrementCertified row11 := certifyIncrement 7911636993 10 64 packet11.packed 204745820 204745935
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet11.counts packet11.arithmetic
def row12 : IncrementRow := ⟨7911768064,7911899136,205453967,205454084⟩
opaque packet12 : SegmentPacket 7911768065 10 64 205453967 205454084 := ⟨Manual.Count131072.C060332.packed,Manual.Count131072.C060332.count_checked,Manual.Count131072.C060332.arithmetic_checked⟩
theorem certified12 : IncrementCertified row12 := certifyIncrement 7911768065 10 64 packet12.packed 205453967 205454084
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet12.counts packet12.arithmetic
def row13 : IncrementRow := ⟨7911899136,7912030208,203066967,203067082⟩
opaque packet13 : SegmentPacket 7911899137 10 64 203066967 203067082 := ⟨Manual.Count131072.C060333.packed,Manual.Count131072.C060333.count_checked,Manual.Count131072.C060333.arithmetic_checked⟩
theorem certified13 : IncrementCertified row13 := certifyIncrement 7911899137 10 64 packet13.packed 203066967 203067082
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet13.counts packet13.arithmetic
def row14 : IncrementRow := ⟨7912030208,7912161280,206300960,206301078⟩
opaque packet14 : SegmentPacket 7912030209 10 64 206300960 206301078 := ⟨Manual.Count131072.C060334.packed,Manual.Count131072.C060334.count_checked,Manual.Count131072.C060334.arithmetic_checked⟩
theorem certified14 : IncrementCertified row14 := certifyIncrement 7912030209 10 64 packet14.packed 206300960 206301078
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet14.counts packet14.arithmetic
def row15 : IncrementRow := ⟨7912161280,7912292352,202668921,202669042⟩
opaque packet15 : SegmentPacket 7912161281 10 64 202668921 202669042 := ⟨Manual.Count131072.C060335.packed,Manual.Count131072.C060335.count_checked,Manual.Count131072.C060335.arithmetic_checked⟩
theorem certified15 : IncrementCertified row15 := certifyIncrement 7912161281 10 64 packet15.packed 202668921 202669042
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet15.counts packet15.arithmetic
def row16 : IncrementRow := ⟨7912292352,7912423424,204977881,204978003⟩
opaque packet16 : SegmentPacket 7912292353 10 64 204977881 204978003 := ⟨Manual.Count131072.C060336.packed,Manual.Count131072.C060336.count_checked,Manual.Count131072.C060336.arithmetic_checked⟩
theorem certified16 : IncrementCertified row16 := certifyIncrement 7912292353 10 64 packet16.packed 204977881 204978003
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet16.counts packet16.arithmetic
def row17 : IncrementRow := ⟨7912423424,7912554496,206077273,206077394⟩
opaque packet17 : SegmentPacket 7912423425 10 64 206077273 206077394 := ⟨Manual.Count131072.C060337.packed,Manual.Count131072.C060337.count_checked,Manual.Count131072.C060337.arithmetic_checked⟩
theorem certified17 : IncrementCertified row17 := certifyIncrement 7912423425 10 64 packet17.packed 206077273 206077394
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet17.counts packet17.arithmetic
def row18 : IncrementRow := ⟨7912554496,7912685568,204224051,204224164⟩
opaque packet18 : SegmentPacket 7912554497 10 64 204224051 204224164 := ⟨Manual.Count131072.C060338.packed,Manual.Count131072.C060338.count_checked,Manual.Count131072.C060338.arithmetic_checked⟩
theorem certified18 : IncrementCertified row18 := certifyIncrement 7912554497 10 64 packet18.packed 204224051 204224164
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet18.counts packet18.arithmetic
def row19 : IncrementRow := ⟨7912685568,7912816640,205608002,205608121⟩
opaque packet19 : SegmentPacket 7912685569 10 64 205608002 205608121 := ⟨Manual.Count131072.C060339.packed,Manual.Count131072.C060339.count_checked,Manual.Count131072.C060339.arithmetic_checked⟩
theorem certified19 : IncrementCertified row19 := certifyIncrement 7912685569 10 64 packet19.packed 205608002 205608121
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet19.counts packet19.arithmetic
def row20 : IncrementRow := ⟨7912816640,7912947712,205248873,205248993⟩
opaque packet20 : SegmentPacket 7912816641 10 64 205248873 205248993 := ⟨Manual.Count131072.C060340.packed,Manual.Count131072.C060340.count_checked,Manual.Count131072.C060340.arithmetic_checked⟩
theorem certified20 : IncrementCertified row20 := certifyIncrement 7912816641 10 64 packet20.packed 205248873 205248993
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet20.counts packet20.arithmetic
def row21 : IncrementRow := ⟨7912947712,7913078784,206063601,206063718⟩
opaque packet21 : SegmentPacket 7912947713 10 64 206063601 206063718 := ⟨Manual.Count131072.C060341.packed,Manual.Count131072.C060341.count_checked,Manual.Count131072.C060341.arithmetic_checked⟩
theorem certified21 : IncrementCertified row21 := certifyIncrement 7912947713 10 64 packet21.packed 206063601 206063718
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet21.counts packet21.arithmetic
def row22 : IncrementRow := ⟨7913078784,7913209856,204601834,204601945⟩
opaque packet22 : SegmentPacket 7913078785 10 64 204601834 204601945 := ⟨Manual.Count131072.C060342.packed,Manual.Count131072.C060342.count_checked,Manual.Count131072.C060342.arithmetic_checked⟩
theorem certified22 : IncrementCertified row22 := certifyIncrement 7913078785 10 64 packet22.packed 204601834 204601945
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet22.counts packet22.arithmetic
def row23 : IncrementRow := ⟨7913209856,7913340928,208013116,208013232⟩
opaque packet23 : SegmentPacket 7913209857 10 64 208013116 208013232 := ⟨Manual.Count131072.C060343.packed,Manual.Count131072.C060343.count_checked,Manual.Count131072.C060343.arithmetic_checked⟩
theorem certified23 : IncrementCertified row23 := certifyIncrement 7913209857 10 64 packet23.packed 208013116 208013232
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet23.counts packet23.arithmetic
def row24 : IncrementRow := ⟨7913340928,7913472000,202318587,202318704⟩
opaque packet24 : SegmentPacket 7913340929 10 64 202318587 202318704 := ⟨Manual.Count131072.C060344.packed,Manual.Count131072.C060344.count_checked,Manual.Count131072.C060344.arithmetic_checked⟩
theorem certified24 : IncrementCertified row24 := certifyIncrement 7913340929 10 64 packet24.packed 202318587 202318704
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet24.counts packet24.arithmetic
def row25 : IncrementRow := ⟨7913472000,7913603072,204413797,204413910⟩
opaque packet25 : SegmentPacket 7913472001 10 64 204413797 204413910 := ⟨Manual.Count131072.C060345.packed,Manual.Count131072.C060345.count_checked,Manual.Count131072.C060345.arithmetic_checked⟩
theorem certified25 : IncrementCertified row25 := certifyIncrement 7913472001 10 64 packet25.packed 204413797 204413910
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet25.counts packet25.arithmetic
def row26 : IncrementRow := ⟨7913603072,7913734144,201493803,201493917⟩
opaque packet26 : SegmentPacket 7913603073 10 64 201493803 201493917 := ⟨Manual.Count131072.C060346.packed,Manual.Count131072.C060346.count_checked,Manual.Count131072.C060346.arithmetic_checked⟩
theorem certified26 : IncrementCertified row26 := certifyIncrement 7913603073 10 64 packet26.packed 201493803 201493917
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet26.counts packet26.arithmetic
def row27 : IncrementRow := ⟨7913734144,7913865216,202095143,202095263⟩
opaque packet27 : SegmentPacket 7913734145 10 64 202095143 202095263 := ⟨Manual.Count131072.C060347.packed,Manual.Count131072.C060347.count_checked,Manual.Count131072.C060347.arithmetic_checked⟩
theorem certified27 : IncrementCertified row27 := certifyIncrement 7913734145 10 64 packet27.packed 202095143 202095263
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet27.counts packet27.arithmetic
def row28 : IncrementRow := ⟨7913865216,7913996288,204119094,204119215⟩
opaque packet28 : SegmentPacket 7913865217 10 64 204119094 204119215 := ⟨Manual.Count131072.C060348.packed,Manual.Count131072.C060348.count_checked,Manual.Count131072.C060348.arithmetic_checked⟩
theorem certified28 : IncrementCertified row28 := certifyIncrement 7913865217 10 64 packet28.packed 204119094 204119215
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet28.counts packet28.arithmetic
def row29 : IncrementRow := ⟨7913996288,7914127360,203048732,203048842⟩
opaque packet29 : SegmentPacket 7913996289 10 64 203048732 203048842 := ⟨Manual.Count131072.C060349.packed,Manual.Count131072.C060349.count_checked,Manual.Count131072.C060349.arithmetic_checked⟩
theorem certified29 : IncrementCertified row29 := certifyIncrement 7913996289 10 64 packet29.packed 203048732 203048842
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet29.counts packet29.arithmetic
def row30 : IncrementRow := ⟨7914127360,7914258432,201978380,201978494⟩
opaque packet30 : SegmentPacket 7914127361 10 64 201978380 201978494 := ⟨Manual.Count131072.C060350.packed,Manual.Count131072.C060350.count_checked,Manual.Count131072.C060350.arithmetic_checked⟩
theorem certified30 : IncrementCertified row30 := certifyIncrement 7914127361 10 64 packet30.packed 201978380 201978494
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet30.counts packet30.arithmetic
def row31 : IncrementRow := ⟨7914258432,7914389504,204073398,204073515⟩
opaque packet31 : SegmentPacket 7914258433 10 64 204073398 204073515 := ⟨Manual.Count131072.C060351.packed,Manual.Count131072.C060351.count_checked,Manual.Count131072.C060351.arithmetic_checked⟩
theorem certified31 : IncrementCertified row31 := certifyIncrement 7914258433 10 64 packet31.packed 204073398 204073515
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet31.counts packet31.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.cons certified8 (CertifiedIncrements.cons certified9 (CertifiedIncrements.cons certified10 (CertifiedIncrements.cons certified11 (CertifiedIncrements.cons certified12 (CertifiedIncrements.cons certified13 (CertifiedIncrements.cons certified14 (CertifiedIncrements.cons certified15 (CertifiedIncrements.cons certified16 (CertifiedIncrements.cons certified17 (CertifiedIncrements.cons certified18 (CertifiedIncrements.cons certified19 (CertifiedIncrements.cons certified20 (CertifiedIncrements.cons certified21 (CertifiedIncrements.cons certified22 (CertifiedIncrements.cons certified23 (CertifiedIncrements.cons certified24 (CertifiedIncrements.cons certified25 (CertifiedIncrements.cons certified26 (CertifiedIncrements.cons certified27 (CertifiedIncrements.cons certified28 (CertifiedIncrements.cons certified29 (CertifiedIncrements.cons certified30 (CertifiedIncrements.cons certified31 (CertifiedIncrements.nil))))))))))))))))))))))))))))))))
theorem checked : checkIncrementSummary 7910195200 7914389504 6540921516 6540925253 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S7.B000010
