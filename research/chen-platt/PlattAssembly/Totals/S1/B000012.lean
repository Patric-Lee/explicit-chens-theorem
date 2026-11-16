import PlattSegmentPacket
import PlattCertificates.Count131072.C000096
import PlattCertificates.Count131072.C000097
import PlattCertificates.Count131072.C000098
import PlattCertificates.Count131072.C000099
import PlattCertificates.Count131072.C000100
import PlattCertificates.Count131072.C000101
import PlattCertificates.Count131072.C000102
import PlattCertificates.Count131072.C000103
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨16515072,16646144,133515157404,133515674810⟩
opaque packet0 : SegmentPacket 16515073 5 2048 133515157404 133515674810 := ⟨Manual.Count131072.C000096.packed,Manual.Count131072.C000096.count_checked,Manual.Count131072.C000096.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 16515073 5 2048 packet0.packed 133515157404 133515674810
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨16646144,16777216,133143898387,133144410321⟩
opaque packet1 : SegmentPacket 16646145 5 2048 133143898387 133144410321 := ⟨Manual.Count131072.C000097.packed,Manual.Count131072.C000097.count_checked,Manual.Count131072.C000097.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 16646145 5 2048 packet1.packed 133143898387 133144410321
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨16777216,16908288,131774617076,131775619555⟩
opaque packet2 : SegmentPacket 16777217 6 1024 131774617076 131775619555 := ⟨Manual.Count131072.C000098.packed,Manual.Count131072.C000098.count_checked,Manual.Count131072.C000098.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 16777217 6 1024 packet2.packed 131774617076 131775619555
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨16908288,17039360,131817279541,131818274623⟩
opaque packet3 : SegmentPacket 16908289 6 1024 131817279541 131818274623 := ⟨Manual.Count131072.C000099.packed,Manual.Count131072.C000099.count_checked,Manual.Count131072.C000099.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 16908289 6 1024 packet3.packed 131817279541 131818274623
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨17039360,17170432,128686361219,128687325258⟩
opaque packet4 : SegmentPacket 17039361 6 1024 128686361219 128687325258 := ⟨Manual.Count131072.C000100.packed,Manual.Count131072.C000100.count_checked,Manual.Count131072.C000100.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 17039361 6 1024 packet4.packed 128686361219 128687325258
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨17170432,17301504,128209130666,128210083815⟩
opaque packet5 : SegmentPacket 17170433 6 1024 128209130666 128210083815 := ⟨Manual.Count131072.C000101.packed,Manual.Count131072.C000101.count_checked,Manual.Count131072.C000101.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 17170433 6 1024 packet5.packed 128209130666 128210083815
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨17301504,17432576,128493773454,128494721547⟩
opaque packet6 : SegmentPacket 17301505 6 1024 128493773454 128494721547 := ⟨Manual.Count131072.C000102.packed,Manual.Count131072.C000102.count_checked,Manual.Count131072.C000102.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 17301505 6 1024 packet6.packed 128493773454 128494721547
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨17432576,17563648,127160715233,127161646454⟩
opaque packet7 : SegmentPacket 17432577 6 1024 127160715233 127161646454 := ⟨Manual.Count131072.C000103.packed,Manual.Count131072.C000103.count_checked,Manual.Count131072.C000103.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 17432577 6 1024 packet7.packed 127160715233 127161646454
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 16515072 17563648 1042800932980 1042807756383 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000012
