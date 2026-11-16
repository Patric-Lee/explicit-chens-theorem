import PlattSegmentPacket
import PlattCertificates.Count131072.C000120
import PlattCertificates.Count131072.C000121
import PlattCertificates.Count131072.C000122
import PlattCertificates.Count131072.C000123
import PlattCertificates.Count131072.C000124
import PlattCertificates.Count131072.C000125
import PlattCertificates.Count131072.C000126
import PlattCertificates.Count131072.C000127
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨19660800,19791872,111897156097,111897883200⟩
opaque packet0 : SegmentPacket 19660801 6 1024 111897156097 111897883200 := ⟨Manual.Count131072.C000120.packed,Manual.Count131072.C000120.count_checked,Manual.Count131072.C000120.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 19660801 6 1024 packet0.packed 111897156097 111897883200
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨19791872,19922944,110932226272,110932942373⟩
opaque packet1 : SegmentPacket 19791873 6 1024 110932226272 110932942373 := ⟨Manual.Count131072.C000121.packed,Manual.Count131072.C000121.count_checked,Manual.Count131072.C000121.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 19791873 6 1024 packet1.packed 110932226272 110932942373
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨19922944,20054016,110204599448,110205306218⟩
opaque packet2 : SegmentPacket 19922945 6 1024 110204599448 110205306218 := ⟨Manual.Count131072.C000122.packed,Manual.Count131072.C000122.count_checked,Manual.Count131072.C000122.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 19922945 6 1024 packet2.packed 110204599448 110205306218
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨20054016,20185088,109317893038,109318589543⟩
opaque packet3 : SegmentPacket 20054017 6 1024 109317893038 109318589543 := ⟨Manual.Count131072.C000123.packed,Manual.Count131072.C000123.count_checked,Manual.Count131072.C000123.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 20054017 6 1024 packet3.packed 109317893038 109318589543
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨20185088,20316160,107469646338,107470326649⟩
opaque packet4 : SegmentPacket 20185089 6 1024 107469646338 107470326649 := ⟨Manual.Count131072.C000124.packed,Manual.Count131072.C000124.count_checked,Manual.Count131072.C000124.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 20185089 6 1024 packet4.packed 107469646338 107470326649
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨20316160,20447232,106657303729,106657974592⟩
opaque packet5 : SegmentPacket 20316161 6 1024 106657303729 106657974592 := ⟨Manual.Count131072.C000125.packed,Manual.Count131072.C000125.count_checked,Manual.Count131072.C000125.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 20316161 6 1024 packet5.packed 106657303729 106657974592
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨20447232,20578304,107182128696,107182798541⟩
opaque packet6 : SegmentPacket 20447233 6 1024 107182128696 107182798541 := ⟨Manual.Count131072.C000126.packed,Manual.Count131072.C000126.count_checked,Manual.Count131072.C000126.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 20447233 6 1024 packet6.packed 107182128696 107182798541
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨20578304,20709376,106745394550,106746057434⟩
opaque packet7 : SegmentPacket 20578305 6 1024 106745394550 106746057434 := ⟨Manual.Count131072.C000127.packed,Manual.Count131072.C000127.count_checked,Manual.Count131072.C000127.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 20578305 6 1024 packet7.packed 106745394550 106746057434
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 19660800 20709376 870406348168 870411878550 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000015
