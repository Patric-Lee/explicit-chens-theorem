import PlattSegmentPacket
import PlattCertificates.Count131072.C000008
import PlattCertificates.Count131072.C000009
import PlattCertificates.Count131072.C000010
import PlattCertificates.Count131072.C000011
import PlattCertificates.Count131072.C000012
import PlattCertificates.Count131072.C000013
import PlattCertificates.Count131072.C000014
import PlattCertificates.Count131072.C000015
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨4980736,5111808,471973827702,471979816399⟩
opaque packet0 : SegmentPacket 4980737 5 2048 471973827702 471979816399 := ⟨Manual.Count131072.C000008.packed,Manual.Count131072.C000008.count_checked,Manual.Count131072.C000008.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 4980737 5 2048 packet0.packed 471973827702 471979816399
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨5111808,5242880,460781041625,460786740336⟩
opaque packet1 : SegmentPacket 5111809 5 2048 460781041625 460786740336 := ⟨Manual.Count131072.C000009.packed,Manual.Count131072.C000009.count_checked,Manual.Count131072.C000009.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 5111809 5 2048 packet1.packed 460781041625 460786740336
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨5242880,5373952,449051495707,449056912521⟩
opaque packet2 : SegmentPacket 5242881 5 2048 449051495707 449056912521 := ⟨Manual.Count131072.C000010.packed,Manual.Count131072.C000010.count_checked,Manual.Count131072.C000010.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 5242881 5 2048 packet2.packed 449051495707 449056912521
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨5373952,5505024,437293757423,437298905301⟩
opaque packet3 : SegmentPacket 5373953 5 2048 437293757423 437298905301 := ⟨Manual.Count131072.C000011.packed,Manual.Count131072.C000011.count_checked,Manual.Count131072.C000011.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 5373953 5 2048 packet3.packed 437293757423 437298905301
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨5505024,5636096,424451615616,424456494579⟩
opaque packet4 : SegmentPacket 5505025 5 2048 424451615616 424456494579 := ⟨Manual.Count131072.C000012.packed,Manual.Count131072.C000012.count_checked,Manual.Count131072.C000012.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 5505025 5 2048 packet4.packed 424451615616 424456494579
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨5636096,5767168,414350608883,414355262335⟩
opaque packet5 : SegmentPacket 5636097 5 2048 414350608883 414355262335 := ⟨Manual.Count131072.C000013.packed,Manual.Count131072.C000013.count_checked,Manual.Count131072.C000013.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 5636097 5 2048 packet5.packed 414350608883 414355262335
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨5767168,5898240,405797830808,405802285702⟩
opaque packet6 : SegmentPacket 5767169 5 2048 405797830808 405802285702 := ⟨Manual.Count131072.C000014.packed,Manual.Count131072.C000014.count_checked,Manual.Count131072.C000014.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 5767169 5 2048 packet6.packed 405797830808 405802285702
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨5898240,6029312,399117504726,399121790289⟩
opaque packet7 : SegmentPacket 5898241 5 2048 399117504726 399121790289 := ⟨Manual.Count131072.C000015.packed,Manual.Count131072.C000015.count_checked,Manual.Count131072.C000015.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 5898241 5 2048 packet7.packed 399117504726 399121790289
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 4980736 6029312 3462817682490 3462858207462 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000001
