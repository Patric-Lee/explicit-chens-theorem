import PlattSegmentPacket
import PlattCertificates.Count131072.C061312
import PlattCertificates.Count131072.C061313
import PlattCertificates.Count131072.C061314
import PlattCertificates.Count131072.C061315
import PlattCertificates.Count131072.C061316
import PlattCertificates.Count131072.C061317
import PlattCertificates.Count131072.C061318
import PlattCertificates.Count131072.C061319
import PlattCertificates.Count131072.C061320
import PlattCertificates.Count131072.C061321
import PlattCertificates.Count131072.C061322
import PlattCertificates.Count131072.C061323
import PlattCertificates.Count131072.C061324
import PlattCertificates.Count131072.C061325
import PlattCertificates.Count131072.C061326
import PlattCertificates.Count131072.C061327
import PlattCertificates.Count131072.C061328
import PlattCertificates.Count131072.C061329
import PlattCertificates.Count131072.C061330
import PlattCertificates.Count131072.C061331
import PlattCertificates.Count131072.C061332
import PlattCertificates.Count131072.C061333
import PlattCertificates.Count131072.C061334
import PlattCertificates.Count131072.C061335
import PlattCertificates.Count131072.C061336
import PlattCertificates.Count131072.C061337
import PlattCertificates.Count131072.C061338
import PlattCertificates.Count131072.C061339
import PlattCertificates.Count131072.C061340
import PlattCertificates.Count131072.C061341
import PlattCertificates.Count131072.C061342
import PlattCertificates.Count131072.C061343
namespace ChenEffective.PlattWindow.Assembly.Totals.S7.B000041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨8040218624,8040349696,201331471,201331583⟩
opaque packet0 : SegmentPacket 8040218625 10 64 201331471 201331583 := ⟨Manual.Count131072.C061312.packed,Manual.Count131072.C061312.count_checked,Manual.Count131072.C061312.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 8040218625 10 64 packet0.packed 201331471 201331583
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨8040349696,8040480768,200803062,200803180⟩
opaque packet1 : SegmentPacket 8040349697 10 64 200803062 200803180 := ⟨Manual.Count131072.C061313.packed,Manual.Count131072.C061313.count_checked,Manual.Count131072.C061313.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 8040349697 10 64 packet1.packed 200803062 200803180
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨8040480768,8040611840,201674969,201675081⟩
opaque packet2 : SegmentPacket 8040480769 10 64 201674969 201675081 := ⟨Manual.Count131072.C061314.packed,Manual.Count131072.C061314.count_checked,Manual.Count131072.C061314.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 8040480769 10 64 packet2.packed 201674969 201675081
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨8040611840,8040742912,201531654,201531771⟩
opaque packet3 : SegmentPacket 8040611841 10 64 201531654 201531771 := ⟨Manual.Count131072.C061315.packed,Manual.Count131072.C061315.count_checked,Manual.Count131072.C061315.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 8040611841 10 64 packet3.packed 201531654 201531771
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨8040742912,8040873984,199393031,199393138⟩
opaque packet4 : SegmentPacket 8040742913 10 64 199393031 199393138 := ⟨Manual.Count131072.C061316.packed,Manual.Count131072.C061316.count_checked,Manual.Count131072.C061316.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 8040742913 10 64 packet4.packed 199393031 199393138
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨8040873984,8041005056,203205324,203205437⟩
opaque packet5 : SegmentPacket 8040873985 10 64 203205324 203205437 := ⟨Manual.Count131072.C061317.packed,Manual.Count131072.C061317.count_checked,Manual.Count131072.C061317.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 8040873985 10 64 packet5.packed 203205324 203205437
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨8041005056,8041136128,203832113,203832224⟩
opaque packet6 : SegmentPacket 8041005057 10 64 203832113 203832224 := ⟨Manual.Count131072.C061318.packed,Manual.Count131072.C061318.count_checked,Manual.Count131072.C061318.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 8041005057 10 64 packet6.packed 203832113 203832224
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨8041136128,8041267200,200748422,200748541⟩
opaque packet7 : SegmentPacket 8041136129 10 64 200748422 200748541 := ⟨Manual.Count131072.C061319.packed,Manual.Count131072.C061319.count_checked,Manual.Count131072.C061319.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 8041136129 10 64 packet7.packed 200748422 200748541
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def row8 : IncrementRow := ⟨8041267200,8041398272,197174773,197174888⟩
opaque packet8 : SegmentPacket 8041267201 10 64 197174773 197174888 := ⟨Manual.Count131072.C061320.packed,Manual.Count131072.C061320.count_checked,Manual.Count131072.C061320.arithmetic_checked⟩
theorem certified8 : IncrementCertified row8 := certifyIncrement 8041267201 10 64 packet8.packed 197174773 197174888
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet8.counts packet8.arithmetic
def row9 : IncrementRow := ⟨8041398272,8041529344,202036987,202037107⟩
opaque packet9 : SegmentPacket 8041398273 10 64 202036987 202037107 := ⟨Manual.Count131072.C061321.packed,Manual.Count131072.C061321.count_checked,Manual.Count131072.C061321.arithmetic_checked⟩
theorem certified9 : IncrementCertified row9 := certifyIncrement 8041398273 10 64 packet9.packed 202036987 202037107
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet9.counts packet9.arithmetic
def row10 : IncrementRow := ⟨8041529344,8041660416,200738596,200738713⟩
opaque packet10 : SegmentPacket 8041529345 10 64 200738596 200738713 := ⟨Manual.Count131072.C061322.packed,Manual.Count131072.C061322.count_checked,Manual.Count131072.C061322.arithmetic_checked⟩
theorem certified10 : IncrementCertified row10 := certifyIncrement 8041529345 10 64 packet10.packed 200738596 200738713
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet10.counts packet10.arithmetic
def row11 : IncrementRow := ⟨8041660416,8041791488,201785396,201785509⟩
opaque packet11 : SegmentPacket 8041660417 10 64 201785396 201785509 := ⟨Manual.Count131072.C061323.packed,Manual.Count131072.C061323.count_checked,Manual.Count131072.C061323.arithmetic_checked⟩
theorem certified11 : IncrementCertified row11 := certifyIncrement 8041660417 10 64 packet11.packed 201785396 201785509
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet11.counts packet11.arithmetic
def row12 : IncrementRow := ⟨8041791488,8041922560,200732071,200732190⟩
opaque packet12 : SegmentPacket 8041791489 10 64 200732071 200732190 := ⟨Manual.Count131072.C061324.packed,Manual.Count131072.C061324.count_checked,Manual.Count131072.C061324.arithmetic_checked⟩
theorem certified12 : IncrementCertified row12 := certifyIncrement 8041791489 10 64 packet12.packed 200732071 200732190
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet12.counts packet12.arithmetic
def row13 : IncrementRow := ⟨8041922560,8042053632,201498802,201498913⟩
opaque packet13 : SegmentPacket 8041922561 10 64 201498802 201498913 := ⟨Manual.Count131072.C061325.packed,Manual.Count131072.C061325.count_checked,Manual.Count131072.C061325.arithmetic_checked⟩
theorem certified13 : IncrementCertified row13 := certifyIncrement 8041922561 10 64 packet13.packed 201498802 201498913
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet13.counts packet13.arithmetic
def row14 : IncrementRow := ⟨8042053632,8042184704,197960507,197960627⟩
opaque packet14 : SegmentPacket 8042053633 10 64 197960507 197960627 := ⟨Manual.Count131072.C061326.packed,Manual.Count131072.C061326.count_checked,Manual.Count131072.C061326.arithmetic_checked⟩
theorem certified14 : IncrementCertified row14 := certifyIncrement 8042053633 10 64 packet14.packed 197960507 197960627
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet14.counts packet14.arithmetic
def row15 : IncrementRow := ⟨8042184704,8042315776,201107246,201107360⟩
opaque packet15 : SegmentPacket 8042184705 10 64 201107246 201107360 := ⟨Manual.Count131072.C061327.packed,Manual.Count131072.C061327.count_checked,Manual.Count131072.C061327.arithmetic_checked⟩
theorem certified15 : IncrementCertified row15 := certifyIncrement 8042184705 10 64 packet15.packed 201107246 201107360
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet15.counts packet15.arithmetic
def row16 : IncrementRow := ⟨8042315776,8042446848,202223914,202224028⟩
opaque packet16 : SegmentPacket 8042315777 10 64 202223914 202224028 := ⟨Manual.Count131072.C061328.packed,Manual.Count131072.C061328.count_checked,Manual.Count131072.C061328.arithmetic_checked⟩
theorem certified16 : IncrementCertified row16 := certifyIncrement 8042315777 10 64 packet16.packed 202223914 202224028
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet16.counts packet16.arithmetic
def row17 : IncrementRow := ⟨8042446848,8042577920,204250542,204250652⟩
opaque packet17 : SegmentPacket 8042446849 10 64 204250542 204250652 := ⟨Manual.Count131072.C061329.packed,Manual.Count131072.C061329.count_checked,Manual.Count131072.C061329.arithmetic_checked⟩
theorem certified17 : IncrementCertified row17 := certifyIncrement 8042446849 10 64 packet17.packed 204250542 204250652
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet17.counts packet17.arithmetic
def row18 : IncrementRow := ⟨8042577920,8042708992,200432450,200432568⟩
opaque packet18 : SegmentPacket 8042577921 10 64 200432450 200432568 := ⟨Manual.Count131072.C061330.packed,Manual.Count131072.C061330.count_checked,Manual.Count131072.C061330.arithmetic_checked⟩
theorem certified18 : IncrementCertified row18 := certifyIncrement 8042577921 10 64 packet18.packed 200432450 200432568
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet18.counts packet18.arithmetic
def row19 : IncrementRow := ⟨8042708992,8042840064,202808991,202809109⟩
opaque packet19 : SegmentPacket 8042708993 10 64 202808991 202809109 := ⟨Manual.Count131072.C061331.packed,Manual.Count131072.C061331.count_checked,Manual.Count131072.C061331.arithmetic_checked⟩
theorem certified19 : IncrementCertified row19 := certifyIncrement 8042708993 10 64 packet19.packed 202808991 202809109
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet19.counts packet19.arithmetic
def row20 : IncrementRow := ⟨8042840064,8042971136,201300841,201300955⟩
opaque packet20 : SegmentPacket 8042840065 10 64 201300841 201300955 := ⟨Manual.Count131072.C061332.packed,Manual.Count131072.C061332.count_checked,Manual.Count131072.C061332.arithmetic_checked⟩
theorem certified20 : IncrementCertified row20 := certifyIncrement 8042840065 10 64 packet20.packed 201300841 201300955
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet20.counts packet20.arithmetic
def row21 : IncrementRow := ⟨8042971136,8043102208,201402549,201402663⟩
opaque packet21 : SegmentPacket 8042971137 10 64 201402549 201402663 := ⟨Manual.Count131072.C061333.packed,Manual.Count131072.C061333.count_checked,Manual.Count131072.C061333.arithmetic_checked⟩
theorem certified21 : IncrementCertified row21 := certifyIncrement 8042971137 10 64 packet21.packed 201402549 201402663
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet21.counts packet21.arithmetic
def row22 : IncrementRow := ⟨8043102208,8043233280,202589106,202589219⟩
opaque packet22 : SegmentPacket 8043102209 10 64 202589106 202589219 := ⟨Manual.Count131072.C061334.packed,Manual.Count131072.C061334.count_checked,Manual.Count131072.C061334.arithmetic_checked⟩
theorem certified22 : IncrementCertified row22 := certifyIncrement 8043102209 10 64 packet22.packed 202589106 202589219
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet22.counts packet22.arithmetic
def row23 : IncrementRow := ⟨8043233280,8043364352,203635654,203635771⟩
opaque packet23 : SegmentPacket 8043233281 10 64 203635654 203635771 := ⟨Manual.Count131072.C061335.packed,Manual.Count131072.C061335.count_checked,Manual.Count131072.C061335.arithmetic_checked⟩
theorem certified23 : IncrementCertified row23 := certifyIncrement 8043233281 10 64 packet23.packed 203635654 203635771
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet23.counts packet23.arithmetic
def row24 : IncrementRow := ⟨8043364352,8043495424,199817950,199818062⟩
opaque packet24 : SegmentPacket 8043364353 10 64 199817950 199818062 := ⟨Manual.Count131072.C061336.packed,Manual.Count131072.C061336.count_checked,Manual.Count131072.C061336.arithmetic_checked⟩
theorem certified24 : IncrementCertified row24 := certifyIncrement 8043364353 10 64 packet24.packed 199817950 199818062
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet24.counts packet24.arithmetic
def row25 : IncrementRow := ⟨8043495424,8043626496,203069119,203069230⟩
opaque packet25 : SegmentPacket 8043495425 10 64 203069119 203069230 := ⟨Manual.Count131072.C061337.packed,Manual.Count131072.C061337.count_checked,Manual.Count131072.C061337.arithmetic_checked⟩
theorem certified25 : IncrementCertified row25 := certifyIncrement 8043495425 10 64 packet25.packed 203069119 203069230
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet25.counts packet25.arithmetic
def row26 : IncrementRow := ⟨8043626496,8043757568,203170794,203170909⟩
opaque packet26 : SegmentPacket 8043626497 10 64 203170794 203170909 := ⟨Manual.Count131072.C061338.packed,Manual.Count131072.C061338.count_checked,Manual.Count131072.C061338.arithmetic_checked⟩
theorem certified26 : IncrementCertified row26 := certifyIncrement 8043626497 10 64 packet26.packed 203170794 203170909
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet26.counts packet26.arithmetic
def row27 : IncrementRow := ⟨8043757568,8043888640,202152703,202152819⟩
opaque packet27 : SegmentPacket 8043757569 10 64 202152703 202152819 := ⟨Manual.Count131072.C061339.packed,Manual.Count131072.C061339.count_checked,Manual.Count131072.C061339.arithmetic_checked⟩
theorem certified27 : IncrementCertified row27 := certifyIncrement 8043757569 10 64 packet27.packed 202152703 202152819
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet27.counts packet27.arithmetic
def row28 : IncrementRow := ⟨8043888640,8044019712,202219385,202219503⟩
opaque packet28 : SegmentPacket 8043888641 10 64 202219385 202219503 := ⟨Manual.Count131072.C061340.packed,Manual.Count131072.C061340.count_checked,Manual.Count131072.C061340.arithmetic_checked⟩
theorem certified28 : IncrementCertified row28 := certifyIncrement 8043888641 10 64 packet28.packed 202219385 202219503
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet28.counts packet28.arithmetic
def row29 : IncrementRow := ⟨8044019712,8044150784,201236325,201236439⟩
opaque packet29 : SegmentPacket 8044019713 10 64 201236325 201236439 := ⟨Manual.Count131072.C061341.packed,Manual.Count131072.C061341.count_checked,Manual.Count131072.C061341.arithmetic_checked⟩
theorem certified29 : IncrementCertified row29 := certifyIncrement 8044019713 10 64 packet29.packed 201236325 201236439
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet29.counts packet29.arithmetic
def row30 : IncrementRow := ⟨8044150784,8044281856,199238571,199238686⟩
opaque packet30 : SegmentPacket 8044150785 10 64 199238571 199238686 := ⟨Manual.Count131072.C061342.packed,Manual.Count131072.C061342.count_checked,Manual.Count131072.C061342.arithmetic_checked⟩
theorem certified30 : IncrementCertified row30 := certifyIncrement 8044150785 10 64 packet30.packed 199238571 199238686
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet30.counts packet30.arithmetic
def row31 : IncrementRow := ⟨8044281856,8044412928,202419444,202419568⟩
opaque packet31 : SegmentPacket 8044281857 10 64 202419444 202419568 := ⟨Manual.Count131072.C061343.packed,Manual.Count131072.C061343.count_checked,Manual.Count131072.C061343.arithmetic_checked⟩
theorem certified31 : IncrementCertified row31 := certifyIncrement 8044281857 10 64 packet31.packed 202419444 202419568
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet31.counts packet31.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.cons certified8 (CertifiedIncrements.cons certified9 (CertifiedIncrements.cons certified10 (CertifiedIncrements.cons certified11 (CertifiedIncrements.cons certified12 (CertifiedIncrements.cons certified13 (CertifiedIncrements.cons certified14 (CertifiedIncrements.cons certified15 (CertifiedIncrements.cons certified16 (CertifiedIncrements.cons certified17 (CertifiedIncrements.cons certified18 (CertifiedIncrements.cons certified19 (CertifiedIncrements.cons certified20 (CertifiedIncrements.cons certified21 (CertifiedIncrements.cons certified22 (CertifiedIncrements.cons certified23 (CertifiedIncrements.cons certified24 (CertifiedIncrements.cons certified25 (CertifiedIncrements.cons certified26 (CertifiedIncrements.cons certified27 (CertifiedIncrements.cons certified28 (CertifiedIncrements.cons certified29 (CertifiedIncrements.cons certified30 (CertifiedIncrements.cons certified31 (CertifiedIncrements.nil))))))))))))))))))))))))))))))))
theorem checked : checkIncrementSummary 8040218624 8044412928 6447522762 6447526443 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S7.B000041
