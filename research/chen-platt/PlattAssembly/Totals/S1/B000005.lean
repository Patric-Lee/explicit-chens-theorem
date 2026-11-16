import PlattSegmentPacket
import PlattCertificates.Count131072.C000040
import PlattCertificates.Count131072.C000041
import PlattCertificates.Count131072.C000042
import PlattCertificates.Count131072.C000043
import PlattCertificates.Count131072.C000044
import PlattCertificates.Count131072.C000045
import PlattCertificates.Count131072.C000046
import PlattCertificates.Count131072.C000047
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨9175040,9306112,250547793353,250549530764⟩
opaque packet0 : SegmentPacket 9175041 5 2048 250547793353 250549530764 := ⟨Manual.Count131072.C000040.packed,Manual.Count131072.C000040.count_checked,Manual.Count131072.C000040.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 9175041 5 2048 packet0.packed 250547793353 250549530764
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨9306112,9437184,244100283122,244101952229⟩
opaque packet1 : SegmentPacket 9306113 5 2048 244100283122 244101952229 := ⟨Manual.Count131072.C000041.packed,Manual.Count131072.C000041.count_checked,Manual.Count131072.C000041.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 9306113 5 2048 packet1.packed 244100283122 244101952229
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨9437184,9568256,240937750653,240939375469⟩
opaque packet2 : SegmentPacket 9437185 5 2048 240937750653 240939375469 := ⟨Manual.Count131072.C000042.packed,Manual.Count131072.C000042.count_checked,Manual.Count131072.C000042.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 9437185 5 2048 packet2.packed 240937750653 240939375469
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨9568256,9699328,239159951830,239161542805⟩
opaque packet3 : SegmentPacket 9568257 5 2048 239159951830 239161542805 := ⟨Manual.Count131072.C000043.packed,Manual.Count131072.C000043.count_checked,Manual.Count131072.C000043.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 9568257 5 2048 packet3.packed 239159951830 239161542805
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨9699328,9830400,235359380071,235360924739⟩
opaque packet4 : SegmentPacket 9699329 5 2048 235359380071 235360924739 := ⟨Manual.Count131072.C000044.packed,Manual.Count131072.C000044.count_checked,Manual.Count131072.C000044.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 9699329 5 2048 packet4.packed 235359380071 235360924739
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨9830400,9961472,229140404301,229141888284⟩
opaque packet5 : SegmentPacket 9830401 5 2048 229140404301 229141888284 := ⟨Manual.Count131072.C000045.packed,Manual.Count131072.C000045.count_checked,Manual.Count131072.C000045.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 9830401 5 2048 packet5.packed 229140404301 229141888284
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨9961472,10092544,228108228260,228109686298⟩
opaque packet6 : SegmentPacket 9961473 5 2048 228108228260 228109686298 := ⟨Manual.Count131072.C000046.packed,Manual.Count131072.C000046.count_checked,Manual.Count131072.C000046.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 9961473 5 2048 packet6.packed 228108228260 228109686298
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨10092544,10223616,223734486703,223735898453⟩
opaque packet7 : SegmentPacket 10092545 5 2048 223734486703 223735898453 := ⟨Manual.Count131072.C000047.packed,Manual.Count131072.C000047.count_checked,Manual.Count131072.C000047.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 10092545 5 2048 packet7.packed 223734486703 223735898453
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 9175040 10223616 1891088278293 1891100799041 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000005
