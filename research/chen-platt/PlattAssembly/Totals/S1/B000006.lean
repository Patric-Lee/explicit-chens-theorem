import PlattSegmentPacket
import PlattCertificates.Count131072.C000048
import PlattCertificates.Count131072.C000049
import PlattCertificates.Count131072.C000050
import PlattCertificates.Count131072.C000051
import PlattCertificates.Count131072.C000052
import PlattCertificates.Count131072.C000053
import PlattCertificates.Count131072.C000054
import PlattCertificates.Count131072.C000055
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨10223616,10354688,222170192946,222171577000⟩
opaque packet0 : SegmentPacket 10223617 5 2048 222170192946 222171577000 := ⟨Manual.Count131072.C000048.packed,Manual.Count131072.C000048.count_checked,Manual.Count131072.C000048.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 10223617 5 2048 packet0.packed 222170192946 222171577000
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨10354688,10485760,220667924060,220669281469⟩
opaque packet1 : SegmentPacket 10354689 5 2048 220667924060 220669281469 := ⟨Manual.Count131072.C000049.packed,Manual.Count131072.C000049.count_checked,Manual.Count131072.C000049.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 10354689 5 2048 packet1.packed 220667924060 220669281469
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨10485760,10616832,216353440696,216354755104⟩
opaque packet2 : SegmentPacket 10485761 5 2048 216353440696 216354755104 := ⟨Manual.Count131072.C000050.packed,Manual.Count131072.C000050.count_checked,Manual.Count131072.C000050.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 10485761 5 2048 packet2.packed 216353440696 216354755104
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨10616832,10747904,214752226790,214753515499⟩
opaque packet3 : SegmentPacket 10616833 5 2048 214752226790 214753515499 := ⟨Manual.Count131072.C000051.packed,Manual.Count131072.C000051.count_checked,Manual.Count131072.C000051.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 10616833 5 2048 packet3.packed 214752226790 214753515499
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨10747904,10878976,209775078269,209776321897⟩
opaque packet4 : SegmentPacket 10747905 5 2048 209775078269 209776321897 := ⟨Manual.Count131072.C000052.packed,Manual.Count131072.C000052.count_checked,Manual.Count131072.C000052.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 10747905 5 2048 packet4.packed 209775078269 209776321897
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨10878976,11010048,208144191524,208145410806⟩
opaque packet5 : SegmentPacket 10878977 5 2048 208144191524 208145410806 := ⟨Manual.Count131072.C000053.packed,Manual.Count131072.C000053.count_checked,Manual.Count131072.C000053.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 10878977 5 2048 packet5.packed 208144191524 208145410806
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨11010048,11141120,205223696302,205224884262⟩
opaque packet6 : SegmentPacket 11010049 5 2048 205223696302 205224884262 := ⟨Manual.Count131072.C000054.packed,Manual.Count131072.C000054.count_checked,Manual.Count131072.C000054.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 11010049 5 2048 packet6.packed 205223696302 205224884262
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨11141120,11272192,203053417501,203054579244⟩
opaque packet7 : SegmentPacket 11141121 5 2048 203053417501 203054579244 := ⟨Manual.Count131072.C000055.packed,Manual.Count131072.C000055.count_checked,Manual.Count131072.C000055.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 11141121 5 2048 packet7.packed 203053417501 203054579244
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 10223616 11272192 1700140168088 1700150325281 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000006
