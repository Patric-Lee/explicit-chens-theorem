import PlattSegmentPacket
import PlattCertificates.Count131072.C060000
import PlattCertificates.Count131072.C060001
import PlattCertificates.Count131072.C060002
import PlattCertificates.Count131072.C060003
import PlattCertificates.Count131072.C060004
import PlattCertificates.Count131072.C060005
import PlattCertificates.Count131072.C060006
import PlattCertificates.Count131072.C060007
import PlattCertificates.Count131072.C060008
import PlattCertificates.Count131072.C060009
import PlattCertificates.Count131072.C060010
import PlattCertificates.Count131072.C060011
import PlattCertificates.Count131072.C060012
import PlattCertificates.Count131072.C060013
import PlattCertificates.Count131072.C060014
import PlattCertificates.Count131072.C060015
import PlattCertificates.Count131072.C060016
import PlattCertificates.Count131072.C060017
import PlattCertificates.Count131072.C060018
import PlattCertificates.Count131072.C060019
import PlattCertificates.Count131072.C060020
import PlattCertificates.Count131072.C060021
import PlattCertificates.Count131072.C060022
import PlattCertificates.Count131072.C060023
import PlattCertificates.Count131072.C060024
import PlattCertificates.Count131072.C060025
import PlattCertificates.Count131072.C060026
import PlattCertificates.Count131072.C060027
import PlattCertificates.Count131072.C060028
import PlattCertificates.Count131072.C060029
import PlattCertificates.Count131072.C060030
import PlattCertificates.Count131072.C060031
namespace ChenEffective.PlattWindow.Assembly.Totals.S7.B000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨7868252160,7868383232,204229178,204229295⟩
opaque packet0 : SegmentPacket 7868252161 10 64 204229178 204229295 := ⟨Manual.Count131072.C060000.packed,Manual.Count131072.C060000.count_checked,Manual.Count131072.C060000.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 7868252161 10 64 packet0.packed 204229178 204229295
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨7868383232,7868514304,206085970,206086083⟩
opaque packet1 : SegmentPacket 7868383233 10 64 206085970 206086083 := ⟨Manual.Count131072.C060001.packed,Manual.Count131072.C060001.count_checked,Manual.Count131072.C060001.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 7868383233 10 64 packet1.packed 206085970 206086083
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨7868514304,7868645376,205975226,205975345⟩
opaque packet2 : SegmentPacket 7868514305 10 64 205975226 205975345 := ⟨Manual.Count131072.C060002.packed,Manual.Count131072.C060002.count_checked,Manual.Count131072.C060002.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 7868514305 10 64 packet2.packed 205975226 205975345
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨7868645376,7868776448,207831901,207832019⟩
opaque packet3 : SegmentPacket 7868645377 10 64 207831901 207832019 := ⟨Manual.Count131072.C060003.packed,Manual.Count131072.C060003.count_checked,Manual.Count131072.C060003.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 7868645377 10 64 packet3.packed 207831901 207832019
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨7868776448,7868907520,204931015,204931133⟩
opaque packet4 : SegmentPacket 7868776449 10 64 204931015 204931133 := ⟨Manual.Count131072.C060004.packed,Manual.Count131072.C060004.count_checked,Manual.Count131072.C060004.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 7868776449 10 64 packet4.packed 204931015 204931133
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨7868907520,7869038592,202137531,202137646⟩
opaque packet5 : SegmentPacket 7868907521 10 64 202137531 202137646 := ⟨Manual.Count131072.C060005.packed,Manual.Count131072.C060005.count_checked,Manual.Count131072.C060005.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 7868907521 10 64 packet5.packed 202137531 202137646
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨7869038592,7869169664,208214984,208215103⟩
opaque packet6 : SegmentPacket 7869038593 10 64 208214984 208215103 := ⟨Manual.Count131072.C060006.packed,Manual.Count131072.C060006.count_checked,Manual.Count131072.C060006.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 7869038593 10 64 packet6.packed 208214984 208215103
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨7869169664,7869300736,206136922,206137037⟩
opaque packet7 : SegmentPacket 7869169665 10 64 206136922 206137037 := ⟨Manual.Count131072.C060007.packed,Manual.Count131072.C060007.count_checked,Manual.Count131072.C060007.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 7869169665 10 64 packet7.packed 206136922 206137037
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def row8 : IncrementRow := ⟨7869300736,7869431808,204988891,204989012⟩
opaque packet8 : SegmentPacket 7869300737 10 64 204988891 204989012 := ⟨Manual.Count131072.C060008.packed,Manual.Count131072.C060008.count_checked,Manual.Count131072.C060008.arithmetic_checked⟩
theorem certified8 : IncrementCertified row8 := certifyIncrement 7869300737 10 64 packet8.packed 204988891 204989012
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet8.counts packet8.arithmetic
def row9 : IncrementRow := ⟨7869431808,7869562880,205271613,205271727⟩
opaque packet9 : SegmentPacket 7869431809 10 64 205271613 205271727 := ⟨Manual.Count131072.C060009.packed,Manual.Count131072.C060009.count_checked,Manual.Count131072.C060009.arithmetic_checked⟩
theorem certified9 : IncrementCertified row9 := certifyIncrement 7869431809 10 64 packet9.packed 205271613 205271727
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet9.counts packet9.arithmetic
def row10 : IncrementRow := ⟨7869562880,7869693952,205196669,205196790⟩
opaque packet10 : SegmentPacket 7869562881 10 64 205196669 205196790 := ⟨Manual.Count131072.C060010.packed,Manual.Count131072.C060010.count_checked,Manual.Count131072.C060010.arithmetic_checked⟩
theorem certified10 : IncrementCertified row10 := certifyIncrement 7869562881 10 64 packet10.packed 205196669 205196790
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet10.counts packet10.arithmetic
def row11 : IncrementRow := ⟨7869693952,7869825024,203011482,203011601⟩
opaque packet11 : SegmentPacket 7869693953 10 64 203011482 203011601 := ⟨Manual.Count131072.C060011.packed,Manual.Count131072.C060011.count_checked,Manual.Count131072.C060011.arithmetic_checked⟩
theorem certified11 : IncrementCertified row11 := certifyIncrement 7869693953 10 64 packet11.packed 203011482 203011601
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet11.counts packet11.arithmetic
def row12 : IncrementRow := ⟨7869825024,7869956096,205297121,205297237⟩
opaque packet12 : SegmentPacket 7869825025 10 64 205297121 205297237 := ⟨Manual.Count131072.C060012.packed,Manual.Count131072.C060012.count_checked,Manual.Count131072.C060012.arithmetic_checked⟩
theorem certified12 : IncrementCertified row12 := certifyIncrement 7869825025 10 64 packet12.packed 205297121 205297237
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet12.counts packet12.arithmetic
def row13 : IncrementRow := ⟨7869956096,7870087168,203147765,203147883⟩
opaque packet13 : SegmentPacket 7869956097 10 64 203147765 203147883 := ⟨Manual.Count131072.C060013.packed,Manual.Count131072.C060013.count_checked,Manual.Count131072.C060013.arithmetic_checked⟩
theorem certified13 : IncrementCertified row13 := certifyIncrement 7869956097 10 64 packet13.packed 203147765 203147883
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet13.counts packet13.arithmetic
def row14 : IncrementRow := ⟨7870087168,7870218240,203001333,203001450⟩
opaque packet14 : SegmentPacket 7870087169 10 64 203001333 203001450 := ⟨Manual.Count131072.C060014.packed,Manual.Count131072.C060014.count_checked,Manual.Count131072.C060014.arithmetic_checked⟩
theorem certified14 : IncrementCertified row14 := certifyIncrement 7870087169 10 64 packet14.packed 203001333 203001450
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet14.counts packet14.arithmetic
def row15 : IncrementRow := ⟨7870218240,7870349312,207540021,207540140⟩
opaque packet15 : SegmentPacket 7870218241 10 64 207540021 207540140 := ⟨Manual.Count131072.C060015.packed,Manual.Count131072.C060015.count_checked,Manual.Count131072.C060015.arithmetic_checked⟩
theorem certified15 : IncrementCertified row15 := certifyIncrement 7870218241 10 64 packet15.packed 207540021 207540140
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet15.counts packet15.arithmetic
def row16 : IncrementRow := ⟨7870349312,7870480384,206213315,206213436⟩
opaque packet16 : SegmentPacket 7870349313 10 64 206213315 206213436 := ⟨Manual.Count131072.C060016.packed,Manual.Count131072.C060016.count_checked,Manual.Count131072.C060016.arithmetic_checked⟩
theorem certified16 : IncrementCertified row16 := certifyIncrement 7870349313 10 64 packet16.packed 206213315 206213436
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet16.counts packet16.arithmetic
def row17 : IncrementRow := ⟨7870480384,7870611456,204493235,204493354⟩
opaque packet17 : SegmentPacket 7870480385 10 64 204493235 204493354 := ⟨Manual.Count131072.C060017.packed,Manual.Count131072.C060017.count_checked,Manual.Count131072.C060017.arithmetic_checked⟩
theorem certified17 : IncrementCertified row17 := certifyIncrement 7870480385 10 64 packet17.packed 204493235 204493354
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet17.counts packet17.arithmetic
def row18 : IncrementRow := ⟨7870611456,7870742528,208995914,208996028⟩
opaque packet18 : SegmentPacket 7870611457 10 64 208995914 208996028 := ⟨Manual.Count131072.C060018.packed,Manual.Count131072.C060018.count_checked,Manual.Count131072.C060018.arithmetic_checked⟩
theorem certified18 : IncrementCertified row18 := certifyIncrement 7870611457 10 64 packet18.packed 208995914 208996028
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet18.counts packet18.arithmetic
def row19 : IncrementRow := ⟨7870742528,7870873600,207848052,207848171⟩
opaque packet19 : SegmentPacket 7870742529 10 64 207848052 207848171 := ⟨Manual.Count131072.C060019.packed,Manual.Count131072.C060019.count_checked,Manual.Count131072.C060019.arithmetic_checked⟩
theorem certified19 : IncrementCertified row19 := certifyIncrement 7870742529 10 64 packet19.packed 207848052 207848171
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet19.counts packet19.arithmetic
def row20 : IncrementRow := ⟨7870873600,7871004672,204947919,204948037⟩
opaque packet20 : SegmentPacket 7870873601 10 64 204947919 204948037 := ⟨Manual.Count131072.C060020.packed,Manual.Count131072.C060020.count_checked,Manual.Count131072.C060020.arithmetic_checked⟩
theorem certified20 : IncrementCertified row20 := certifyIncrement 7870873601 10 64 packet20.packed 204947919 204948037
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet20.counts packet20.arithmetic
def row21 : IncrementRow := ⟨7871004672,7871135744,205802761,205802883⟩
opaque packet21 : SegmentPacket 7871004673 10 64 205802761 205802883 := ⟨Manual.Count131072.C060021.packed,Manual.Count131072.C060021.count_checked,Manual.Count131072.C060021.arithmetic_checked⟩
theorem certified21 : IncrementCertified row21 := certifyIncrement 7871004673 10 64 packet21.packed 205802761 205802883
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet21.counts packet21.arithmetic
def row22 : IncrementRow := ⟨7871135744,7871266816,206192708,206192827⟩
opaque packet22 : SegmentPacket 7871135745 10 64 206192708 206192827 := ⟨Manual.Count131072.C060022.packed,Manual.Count131072.C060022.count_checked,Manual.Count131072.C060022.arithmetic_checked⟩
theorem certified22 : IncrementCertified row22 := certifyIncrement 7871135745 10 64 packet22.packed 206192708 206192827
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet22.counts packet22.arithmetic
def row23 : IncrementRow := ⟨7871266816,7871397888,207190540,207190659⟩
opaque packet23 : SegmentPacket 7871266817 10 64 207190540 207190659 := ⟨Manual.Count131072.C060023.packed,Manual.Count131072.C060023.count_checked,Manual.Count131072.C060023.arithmetic_checked⟩
theorem certified23 : IncrementCertified row23 := certifyIncrement 7871266817 10 64 packet23.packed 207190540 207190659
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet23.counts packet23.arithmetic
def row24 : IncrementRow := ⟨7871397888,7871528960,202502664,202502781⟩
opaque packet24 : SegmentPacket 7871397889 10 64 202502664 202502781 := ⟨Manual.Count131072.C060024.packed,Manual.Count131072.C060024.count_checked,Manual.Count131072.C060024.arithmetic_checked⟩
theorem certified24 : IncrementCertified row24 := certifyIncrement 7871397889 10 64 packet24.packed 202502664 202502781
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet24.counts packet24.arithmetic
def row25 : IncrementRow := ⟨7871528960,7871660032,206182407,206182527⟩
opaque packet25 : SegmentPacket 7871528961 10 64 206182407 206182527 := ⟨Manual.Count131072.C060025.packed,Manual.Count131072.C060025.count_checked,Manual.Count131072.C060025.arithmetic_checked⟩
theorem certified25 : IncrementCertified row25 := certifyIncrement 7871528961 10 64 packet25.packed 206182407 206182527
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet25.counts packet25.arithmetic
def row26 : IncrementRow := ⟨7871660032,7871791104,205606860,205606976⟩
opaque packet26 : SegmentPacket 7871660033 10 64 205606860 205606976 := ⟨Manual.Count131072.C060026.packed,Manual.Count131072.C060026.count_checked,Manual.Count131072.C060026.arithmetic_checked⟩
theorem certified26 : IncrementCertified row26 := certifyIncrement 7871660033 10 64 packet26.packed 205606860 205606976
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet26.counts packet26.arithmetic
def row27 : IncrementRow := ⟨7871791104,7871922176,206747662,206747777⟩
opaque packet27 : SegmentPacket 7871791105 10 64 206747662 206747777 := ⟨Manual.Count131072.C060027.packed,Manual.Count131072.C060027.count_checked,Manual.Count131072.C060027.arithmetic_checked⟩
theorem certified27 : IncrementCertified row27 := certifyIncrement 7871791105 10 64 packet27.packed 206747662 206747777
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet27.counts packet27.arithmetic
def row28 : IncrementRow := ⟨7871922176,7872053248,207244797,207244917⟩
opaque packet28 : SegmentPacket 7871922177 10 64 207244797 207244917 := ⟨Manual.Count131072.C060028.packed,Manual.Count131072.C060028.count_checked,Manual.Count131072.C060028.arithmetic_checked⟩
theorem certified28 : IncrementCertified row28 := certifyIncrement 7871922177 10 64 packet28.packed 207244797 207244917
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet28.counts packet28.arithmetic
def row29 : IncrementRow := ⟨7872053248,7872184320,202056737,202056857⟩
opaque packet29 : SegmentPacket 7872053249 10 64 202056737 202056857 := ⟨Manual.Count131072.C060029.packed,Manual.Count131072.C060029.count_checked,Manual.Count131072.C060029.arithmetic_checked⟩
theorem certified29 : IncrementCertified row29 := certifyIncrement 7872053249 10 64 packet29.packed 202056737 202056857
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet29.counts packet29.arithmetic
def row30 : IncrementRow := ⟨7872184320,7872315392,207917252,207917369⟩
opaque packet30 : SegmentPacket 7872184321 10 64 207917252 207917369 := ⟨Manual.Count131072.C060030.packed,Manual.Count131072.C060030.count_checked,Manual.Count131072.C060030.arithmetic_checked⟩
theorem certified30 : IncrementCertified row30 := certifyIncrement 7872184321 10 64 packet30.packed 207917252 207917369
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet30.counts packet30.arithmetic
def row31 : IncrementRow := ⟨7872315392,7872446464,204874632,204874748⟩
opaque packet31 : SegmentPacket 7872315393 10 64 204874632 204874748 := ⟨Manual.Count131072.C060031.packed,Manual.Count131072.C060031.count_checked,Manual.Count131072.C060031.arithmetic_checked⟩
theorem certified31 : IncrementCertified row31 := certifyIncrement 7872315393 10 64 packet31.packed 204874632 204874748
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet31.counts packet31.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.cons certified8 (CertifiedIncrements.cons certified9 (CertifiedIncrements.cons certified10 (CertifiedIncrements.cons certified11 (CertifiedIncrements.cons certified12 (CertifiedIncrements.cons certified13 (CertifiedIncrements.cons certified14 (CertifiedIncrements.cons certified15 (CertifiedIncrements.cons certified16 (CertifiedIncrements.cons certified17 (CertifiedIncrements.cons certified18 (CertifiedIncrements.cons certified19 (CertifiedIncrements.cons certified20 (CertifiedIncrements.cons certified21 (CertifiedIncrements.cons certified22 (CertifiedIncrements.cons certified23 (CertifiedIncrements.cons certified24 (CertifiedIncrements.cons certified25 (CertifiedIncrements.cons certified26 (CertifiedIncrements.cons certified27 (CertifiedIncrements.cons certified28 (CertifiedIncrements.cons certified29 (CertifiedIncrements.cons certified30 (CertifiedIncrements.cons certified31 (CertifiedIncrements.nil))))))))))))))))))))))))))))))))
theorem checked : checkIncrementSummary 7868252160 7872446464 6577815077 6577818848 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S7.B000000
