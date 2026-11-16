import PlattSegmentPacket
import PlattCertificates.Count131072.C060800
import PlattCertificates.Count131072.C060801
import PlattCertificates.Count131072.C060802
import PlattCertificates.Count131072.C060803
import PlattCertificates.Count131072.C060804
import PlattCertificates.Count131072.C060805
import PlattCertificates.Count131072.C060806
import PlattCertificates.Count131072.C060807
import PlattCertificates.Count131072.C060808
import PlattCertificates.Count131072.C060809
import PlattCertificates.Count131072.C060810
import PlattCertificates.Count131072.C060811
import PlattCertificates.Count131072.C060812
import PlattCertificates.Count131072.C060813
import PlattCertificates.Count131072.C060814
import PlattCertificates.Count131072.C060815
import PlattCertificates.Count131072.C060816
import PlattCertificates.Count131072.C060817
import PlattCertificates.Count131072.C060818
import PlattCertificates.Count131072.C060819
import PlattCertificates.Count131072.C060820
import PlattCertificates.Count131072.C060821
import PlattCertificates.Count131072.C060822
import PlattCertificates.Count131072.C060823
import PlattCertificates.Count131072.C060824
import PlattCertificates.Count131072.C060825
import PlattCertificates.Count131072.C060826
import PlattCertificates.Count131072.C060827
import PlattCertificates.Count131072.C060828
import PlattCertificates.Count131072.C060829
import PlattCertificates.Count131072.C060830
import PlattCertificates.Count131072.C060831
namespace ChenEffective.PlattWindow.Assembly.Totals.S7.B000025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨7973109760,7973240832,200872557,200872675⟩
opaque packet0 : SegmentPacket 7973109761 10 64 200872557 200872675 := ⟨Manual.Count131072.C060800.packed,Manual.Count131072.C060800.count_checked,Manual.Count131072.C060800.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 7973109761 10 64 packet0.packed 200872557 200872675
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨7973240832,7973371904,204258264,204258377⟩
opaque packet1 : SegmentPacket 7973240833 10 64 204258264 204258377 := ⟨Manual.Count131072.C060801.packed,Manual.Count131072.C060801.count_checked,Manual.Count131072.C060801.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 7973240833 10 64 packet1.packed 204258264 204258377
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨7973371904,7973502976,203725384,203725502⟩
opaque packet2 : SegmentPacket 7973371905 10 64 203725384 203725502 := ⟨Manual.Count131072.C060802.packed,Manual.Count131072.C060802.count_checked,Manual.Count131072.C060802.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 7973371905 10 64 packet2.packed 203725384 203725502
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨7973502976,7973634048,204286864,204286975⟩
opaque packet3 : SegmentPacket 7973502977 10 64 204286864 204286975 := ⟨Manual.Count131072.C060803.packed,Manual.Count131072.C060803.count_checked,Manual.Count131072.C060803.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 7973502977 10 64 packet3.packed 204286864 204286975
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨7973634048,7973765120,202200778,202200893⟩
opaque packet4 : SegmentPacket 7973634049 10 64 202200778 202200893 := ⟨Manual.Count131072.C060804.packed,Manual.Count131072.C060804.count_checked,Manual.Count131072.C060804.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 7973634049 10 64 packet4.packed 202200778 202200893
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨7973765120,7973896192,205339122,205339235⟩
opaque packet5 : SegmentPacket 7973765121 10 64 205339122 205339235 := ⟨Manual.Count131072.C060805.packed,Manual.Count131072.C060805.count_checked,Manual.Count131072.C060805.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 7973765121 10 64 packet5.packed 205339122 205339235
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨7973896192,7974027264,202582411,202582521⟩
opaque packet6 : SegmentPacket 7973896193 10 64 202582411 202582521 := ⟨Manual.Count131072.C060806.packed,Manual.Count131072.C060806.count_checked,Manual.Count131072.C060806.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 7973896193 10 64 packet6.packed 202582411 202582521
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨7974027264,7974158336,204767615,204767728⟩
opaque packet7 : SegmentPacket 7974027265 10 64 204767615 204767728 := ⟨Manual.Count131072.C060807.packed,Manual.Count131072.C060807.count_checked,Manual.Count131072.C060807.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 7974027265 10 64 packet7.packed 204767615 204767728
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def row8 : IncrementRow := ⟨7974158336,7974289408,201375628,201375742⟩
opaque packet8 : SegmentPacket 7974158337 10 64 201375628 201375742 := ⟨Manual.Count131072.C060808.packed,Manual.Count131072.C060808.count_checked,Manual.Count131072.C060808.arithmetic_checked⟩
theorem certified8 : IncrementCertified row8 := certifyIncrement 7974158337 10 64 packet8.packed 201375628 201375742
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet8.counts packet8.arithmetic
def row9 : IncrementRow := ⟨7974289408,7974420480,203454870,203454985⟩
opaque packet9 : SegmentPacket 7974289409 10 64 203454870 203454985 := ⟨Manual.Count131072.C060809.packed,Manual.Count131072.C060809.count_checked,Manual.Count131072.C060809.arithmetic_checked⟩
theorem certified9 : IncrementCertified row9 := certifyIncrement 7974289409 10 64 packet9.packed 203454870 203454985
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet9.counts packet9.arithmetic
def row10 : IncrementRow := ⟨7974420480,7974551552,202110217,202110332⟩
opaque packet10 : SegmentPacket 7974420481 10 64 202110217 202110332 := ⟨Manual.Count131072.C060810.packed,Manual.Count131072.C060810.count_checked,Manual.Count131072.C060810.arithmetic_checked⟩
theorem certified10 : IncrementCertified row10 := certifyIncrement 7974420481 10 64 packet10.packed 202110217 202110332
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet10.counts packet10.arithmetic
def row11 : IncrementRow := ⟨7974551552,7974682624,203412888,203413002⟩
opaque packet11 : SegmentPacket 7974551553 10 64 203412888 203413002 := ⟨Manual.Count131072.C060811.packed,Manual.Count131072.C060811.count_checked,Manual.Count131072.C060811.arithmetic_checked⟩
theorem certified11 : IncrementCertified row11 := certifyIncrement 7974551553 10 64 packet11.packed 203412888 203413002
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet11.counts packet11.arithmetic
def row12 : IncrementRow := ⟨7974682624,7974813696,200974124,200974236⟩
opaque packet12 : SegmentPacket 7974682625 10 64 200974124 200974236 := ⟨Manual.Count131072.C060812.packed,Manual.Count131072.C060812.count_checked,Manual.Count131072.C060812.arithmetic_checked⟩
theorem certified12 : IncrementCertified row12 := certifyIncrement 7974682625 10 64 packet12.packed 200974124 200974236
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet12.counts packet12.arithmetic
def row13 : IncrementRow := ⟨7974813696,7974944768,203865022,203865139⟩
opaque packet13 : SegmentPacket 7974813697 10 64 203865022 203865139 := ⟨Manual.Count131072.C060813.packed,Manual.Count131072.C060813.count_checked,Manual.Count131072.C060813.arithmetic_checked⟩
theorem certified13 : IncrementCertified row13 := certifyIncrement 7974813697 10 64 packet13.packed 203865022 203865139
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet13.counts packet13.arithmetic
def row14 : IncrementRow := ⟨7974944768,7975075840,204532267,204532386⟩
opaque packet14 : SegmentPacket 7974944769 10 64 204532267 204532386 := ⟨Manual.Count131072.C060814.packed,Manual.Count131072.C060814.count_checked,Manual.Count131072.C060814.arithmetic_checked⟩
theorem certified14 : IncrementCertified row14 := certifyIncrement 7974944769 10 64 packet14.packed 204532267 204532386
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet14.counts packet14.arithmetic
def row15 : IncrementRow := ⟨7975075840,7975206912,201246566,201246681⟩
opaque packet15 : SegmentPacket 7975075841 10 64 201246566 201246681 := ⟨Manual.Count131072.C060815.packed,Manual.Count131072.C060815.count_checked,Manual.Count131072.C060815.arithmetic_checked⟩
theorem certified15 : IncrementCertified row15 := certifyIncrement 7975075841 10 64 packet15.packed 201246566 201246681
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet15.counts packet15.arithmetic
def row16 : IncrementRow := ⟨7975206912,7975337984,200890321,200890441⟩
opaque packet16 : SegmentPacket 7975206913 10 64 200890321 200890441 := ⟨Manual.Count131072.C060816.packed,Manual.Count131072.C060816.count_checked,Manual.Count131072.C060816.arithmetic_checked⟩
theorem certified16 : IncrementCertified row16 := certifyIncrement 7975206913 10 64 packet16.packed 200890321 200890441
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet16.counts packet16.arithmetic
def row17 : IncrementRow := ⟨7975337984,7975469056,204169268,204169384⟩
opaque packet17 : SegmentPacket 7975337985 10 64 204169268 204169384 := ⟨Manual.Count131072.C060817.packed,Manual.Count131072.C060817.count_checked,Manual.Count131072.C060817.arithmetic_checked⟩
theorem certified17 : IncrementCertified row17 := certifyIncrement 7975337985 10 64 packet17.packed 204169268 204169384
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet17.counts packet17.arithmetic
def row18 : IncrementRow := ⟨7975469056,7975600128,201942498,201942616⟩
opaque packet18 : SegmentPacket 7975469057 10 64 201942498 201942616 := ⟨Manual.Count131072.C060818.packed,Manual.Count131072.C060818.count_checked,Manual.Count131072.C060818.arithmetic_checked⟩
theorem certified18 : IncrementCertified row18 := certifyIncrement 7975469057 10 64 packet18.packed 201942498 201942616
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet18.counts packet18.arithmetic
def row19 : IncrementRow := ⟨7975600128,7975731200,202892047,202892162⟩
opaque packet19 : SegmentPacket 7975600129 10 64 202892047 202892162 := ⟨Manual.Count131072.C060819.packed,Manual.Count131072.C060819.count_checked,Manual.Count131072.C060819.arithmetic_checked⟩
theorem certified19 : IncrementCertified row19 := certifyIncrement 7975600129 10 64 packet19.packed 202892047 202892162
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet19.counts packet19.arithmetic
def row20 : IncrementRow := ⟨7975731200,7975862272,203559248,203559359⟩
opaque packet20 : SegmentPacket 7975731201 10 64 203559248 203559359 := ⟨Manual.Count131072.C060820.packed,Manual.Count131072.C060820.count_checked,Manual.Count131072.C060820.arithmetic_checked⟩
theorem certified20 : IncrementCertified row20 := certifyIncrement 7975731201 10 64 packet20.packed 203559248 203559359
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet20.counts packet20.arithmetic
def row21 : IncrementRow := ⟨7975862272,7975993344,203979385,203979507⟩
opaque packet21 : SegmentPacket 7975862273 10 64 203979385 203979507 := ⟨Manual.Count131072.C060821.packed,Manual.Count131072.C060821.count_checked,Manual.Count131072.C060821.arithmetic_checked⟩
theorem certified21 : IncrementCertified row21 := certifyIncrement 7975862273 10 64 packet21.packed 203979385 203979507
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet21.counts packet21.arithmetic
def row22 : IncrementRow := ⟨7975993344,7976124416,203481990,203482109⟩
opaque packet22 : SegmentPacket 7975993345 10 64 203481990 203482109 := ⟨Manual.Count131072.C060822.packed,Manual.Count131072.C060822.count_checked,Manual.Count131072.C060822.arithmetic_checked⟩
theorem certified22 : IncrementCertified row22 := certifyIncrement 7975993345 10 64 packet22.packed 203481990 203482109
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet22.counts packet22.arithmetic
def row23 : IncrementRow := ⟨7976124416,7976255488,207254602,207254719⟩
opaque packet23 : SegmentPacket 7976124417 10 64 207254602 207254719 := ⟨Manual.Count131072.C060823.packed,Manual.Count131072.C060823.count_checked,Manual.Count131072.C060823.arithmetic_checked⟩
theorem certified23 : IncrementCertified row23 := certifyIncrement 7976124417 10 64 packet23.packed 207254602 207254719
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet23.counts packet23.arithmetic
def row24 : IncrementRow := ⟨7976255488,7976386560,203581167,203581286⟩
opaque packet24 : SegmentPacket 7976255489 10 64 203581167 203581286 := ⟨Manual.Count131072.C060824.packed,Manual.Count131072.C060824.count_checked,Manual.Count131072.C060824.arithmetic_checked⟩
theorem certified24 : IncrementCertified row24 := certifyIncrement 7976255489 10 64 packet24.packed 203581167 203581286
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet24.counts packet24.arithmetic
def row25 : IncrementRow := ⟨7976386560,7976517632,203013187,203013306⟩
opaque packet25 : SegmentPacket 7976386561 10 64 203013187 203013306 := ⟨Manual.Count131072.C060825.packed,Manual.Count131072.C060825.count_checked,Manual.Count131072.C060825.arithmetic_checked⟩
theorem certified25 : IncrementCertified row25 := certifyIncrement 7976386561 10 64 packet25.packed 203013187 203013306
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet25.counts packet25.arithmetic
def row26 : IncrementRow := ⟨7976517632,7976648704,201316057,201316173⟩
opaque packet26 : SegmentPacket 7976517633 10 64 201316057 201316173 := ⟨Manual.Count131072.C060826.packed,Manual.Count131072.C060826.count_checked,Manual.Count131072.C060826.arithmetic_checked⟩
theorem certified26 : IncrementCertified row26 := certifyIncrement 7976517633 10 64 packet26.packed 201316057 201316173
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet26.counts packet26.arithmetic
def row27 : IncrementRow := ⟨7976648704,7976779776,202300778,202300893⟩
opaque packet27 : SegmentPacket 7976648705 10 64 202300778 202300893 := ⟨Manual.Count131072.C060827.packed,Manual.Count131072.C060827.count_checked,Manual.Count131072.C060827.arithmetic_checked⟩
theorem certified27 : IncrementCertified row27 := certifyIncrement 7976648705 10 64 packet27.packed 202300778 202300893
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet27.counts packet27.arithmetic
def row28 : IncrementRow := ⟨7976779776,7976910848,204132366,204132485⟩
opaque packet28 : SegmentPacket 7976779777 10 64 204132366 204132485 := ⟨Manual.Count131072.C060828.packed,Manual.Count131072.C060828.count_checked,Manual.Count131072.C060828.arithmetic_checked⟩
theorem certified28 : IncrementCertified row28 := certifyIncrement 7976779777 10 64 packet28.packed 204132366 204132485
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet28.counts packet28.arithmetic
def row29 : IncrementRow := ⟨7976910848,7977041920,205222879,205222992⟩
opaque packet29 : SegmentPacket 7976910849 10 64 205222879 205222992 := ⟨Manual.Count131072.C060829.packed,Manual.Count131072.C060829.count_checked,Manual.Count131072.C060829.arithmetic_checked⟩
theorem certified29 : IncrementCertified row29 := certifyIncrement 7976910849 10 64 packet29.packed 205222879 205222992
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet29.counts packet29.arithmetic
def row30 : IncrementRow := ⟨7977041920,7977172992,201973248,201973363⟩
opaque packet30 : SegmentPacket 7977041921 10 64 201973248 201973363 := ⟨Manual.Count131072.C060830.packed,Manual.Count131072.C060830.count_checked,Manual.Count131072.C060830.arithmetic_checked⟩
theorem certified30 : IncrementCertified row30 := certifyIncrement 7977041921 10 64 packet30.packed 201973248 201973363
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet30.counts packet30.arithmetic
def row31 : IncrementRow := ⟨7977172992,7977304064,204581004,204581125⟩
opaque packet31 : SegmentPacket 7977172993 10 64 204581004 204581125 := ⟨Manual.Count131072.C060831.packed,Manual.Count131072.C060831.count_checked,Manual.Count131072.C060831.arithmetic_checked⟩
theorem certified31 : IncrementCertified row31 := certifyIncrement 7977172993 10 64 packet31.packed 204581004 204581125
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet31.counts packet31.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.cons certified8 (CertifiedIncrements.cons certified9 (CertifiedIncrements.cons certified10 (CertifiedIncrements.cons certified11 (CertifiedIncrements.cons certified12 (CertifiedIncrements.cons certified13 (CertifiedIncrements.cons certified14 (CertifiedIncrements.cons certified15 (CertifiedIncrements.cons certified16 (CertifiedIncrements.cons certified17 (CertifiedIncrements.cons certified18 (CertifiedIncrements.cons certified19 (CertifiedIncrements.cons certified20 (CertifiedIncrements.cons certified21 (CertifiedIncrements.cons certified22 (CertifiedIncrements.cons certified23 (CertifiedIncrements.cons certified24 (CertifiedIncrements.cons certified25 (CertifiedIncrements.cons certified26 (CertifiedIncrements.cons certified27 (CertifiedIncrements.cons certified28 (CertifiedIncrements.cons certified29 (CertifiedIncrements.cons certified30 (CertifiedIncrements.cons certified31 (CertifiedIncrements.nil))))))))))))))))))))))))))))))))
theorem checked : checkIncrementSummary 7973109760 7977304064 6503294622 6503298329 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S7.B000025
