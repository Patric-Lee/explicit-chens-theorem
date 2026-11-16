import PlattSegmentPacket
import PlattCertificates.Count131072.C000064
import PlattCertificates.Count131072.C000065
import PlattCertificates.Count131072.C000066
import PlattCertificates.Count131072.C000067
import PlattCertificates.Count131072.C000068
import PlattCertificates.Count131072.C000069
import PlattCertificates.Count131072.C000070
import PlattCertificates.Count131072.C000071
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨12320768,12451840,182752153334,182753099646⟩
opaque packet0 : SegmentPacket 12320769 5 2048 182752153334 182753099646 := ⟨Manual.Count131072.C000064.packed,Manual.Count131072.C000064.count_checked,Manual.Count131072.C000064.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 12320769 5 2048 packet0.packed 182752153334 182753099646
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨12451840,12582912,179199212023,179200130326⟩
opaque packet1 : SegmentPacket 12451841 5 2048 179199212023 179200130326 := ⟨Manual.Count131072.C000065.packed,Manual.Count131072.C000065.count_checked,Manual.Count131072.C000065.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 12451841 5 2048 packet1.packed 179199212023 179200130326
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨12582912,12713984,178855924244,178856831336⟩
opaque packet2 : SegmentPacket 12582913 5 2048 178855924244 178856831336 := ⟨Manual.Count131072.C000066.packed,Manual.Count131072.C000066.count_checked,Manual.Count131072.C000066.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 12582913 5 2048 packet2.packed 178855924244 178856831336
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨12713984,12845056,177508535386,177509426424⟩
opaque packet3 : SegmentPacket 12713985 5 2048 177508535386 177509426424 := ⟨Manual.Count131072.C000067.packed,Manual.Count131072.C000067.count_checked,Manual.Count131072.C000067.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 12713985 5 2048 packet3.packed 177508535386 177509426424
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨12845056,12976128,173414926784,173415788517⟩
opaque packet4 : SegmentPacket 12845057 5 2048 173414926784 173415788517 := ⟨Manual.Count131072.C000068.packed,Manual.Count131072.C000068.count_checked,Manual.Count131072.C000068.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 12845057 5 2048 packet4.packed 173414926784 173415788517
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨12976128,13107200,171218033365,171218875676⟩
opaque packet5 : SegmentPacket 12976129 5 2048 171218033365 171218875676 := ⟨Manual.Count131072.C000069.packed,Manual.Count131072.C000069.count_checked,Manual.Count131072.C000069.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 12976129 5 2048 packet5.packed 171218033365 171218875676
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨13107200,13238272,171007496494,171008329382⟩
opaque packet6 : SegmentPacket 13107201 5 2048 171007496494 171008329382 := ⟨Manual.Count131072.C000070.packed,Manual.Count131072.C000070.count_checked,Manual.Count131072.C000070.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 13107201 5 2048 packet6.packed 171007496494 171008329382
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨13238272,13369344,169257290463,169258106773⟩
opaque packet7 : SegmentPacket 13238273 5 2048 169257290463 169258106773 := ⟨Manual.Count131072.C000071.packed,Manual.Count131072.C000071.count_checked,Manual.Count131072.C000071.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 13238273 5 2048 packet7.packed 169257290463 169258106773
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 12320768 13369344 1403213572093 1403220588080 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000008
