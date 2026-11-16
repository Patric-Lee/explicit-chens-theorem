import PlattSegmentPacket
import PlattCertificates.Count131072.C000104
import PlattCertificates.Count131072.C000105
import PlattCertificates.Count131072.C000106
import PlattCertificates.Count131072.C000107
import PlattCertificates.Count131072.C000108
import PlattCertificates.Count131072.C000109
import PlattCertificates.Count131072.C000110
import PlattCertificates.Count131072.C000111
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨17563648,17694720,125178079612,125178989536⟩
opaque packet0 : SegmentPacket 17563649 6 1024 125178079612 125178989536 := ⟨Manual.Count131072.C000104.packed,Manual.Count131072.C000104.count_checked,Manual.Count131072.C000104.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 17563649 6 1024 packet0.packed 125178079612 125178989536
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨17694720,17825792,124093505895,124094401258⟩
opaque packet1 : SegmentPacket 17694721 6 1024 124093505895 124094401258 := ⟨Manual.Count131072.C000105.packed,Manual.Count131072.C000105.count_checked,Manual.Count131072.C000105.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 17694721 6 1024 packet1.packed 124093505895 124094401258
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨17825792,17956864,123842821567,123843708559⟩
opaque packet2 : SegmentPacket 17825793 6 1024 123842821567 123843708559 := ⟨Manual.Count131072.C000106.packed,Manual.Count131072.C000106.count_checked,Manual.Count131072.C000106.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 17825793 6 1024 packet2.packed 123842821567 123843708559
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨17956864,18087936,121528516183,121529380370⟩
opaque packet3 : SegmentPacket 17956865 6 1024 121528516183 121529380370 := ⟨Manual.Count131072.C000107.packed,Manual.Count131072.C000107.count_checked,Manual.Count131072.C000107.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 17956865 6 1024 packet3.packed 121528516183 121529380370
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨18087936,18219008,121175880761,121176736207⟩
opaque packet4 : SegmentPacket 18087937 6 1024 121175880761 121176736207 := ⟨Manual.Count131072.C000108.packed,Manual.Count131072.C000108.count_checked,Manual.Count131072.C000108.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 18087937 6 1024 packet4.packed 121175880761 121176736207
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨18219008,18350080,121924741108,121925595668⟩
opaque packet5 : SegmentPacket 18219009 6 1024 121924741108 121925595668 := ⟨Manual.Count131072.C000109.packed,Manual.Count131072.C000109.count_checked,Manual.Count131072.C000109.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 18219009 6 1024 packet5.packed 121924741108 121925595668
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨18350080,18481152,118929575692,118930403373⟩
opaque packet6 : SegmentPacket 18350081 6 1024 118929575692 118930403373 := ⟨Manual.Count131072.C000110.packed,Manual.Count131072.C000110.count_checked,Manual.Count131072.C000110.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 18350081 6 1024 packet6.packed 118929575692 118930403373
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨18481152,18612224,118921427305,118922249063⟩
opaque packet7 : SegmentPacket 18481153 6 1024 118921427305 118922249063 := ⟨Manual.Count131072.C000111.packed,Manual.Count131072.C000111.count_checked,Manual.Count131072.C000111.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 18481153 6 1024 packet7.packed 118921427305 118922249063
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 17563648 18612224 975594548123 975601464034 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000013
