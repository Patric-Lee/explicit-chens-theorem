import PlattSegmentPacket
import PlattCertificates.Count131072.C000032
import PlattCertificates.Count131072.C000033
import PlattCertificates.Count131072.C000034
import PlattCertificates.Count131072.C000035
import PlattCertificates.Count131072.C000036
import PlattCertificates.Count131072.C000037
import PlattCertificates.Count131072.C000038
import PlattCertificates.Count131072.C000039
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨8126464,8257536,282746462936,282748674018⟩
opaque packet0 : SegmentPacket 8126465 5 2048 282746462936 282748674018 := ⟨Manual.Count131072.C000032.packed,Manual.Count131072.C000032.count_checked,Manual.Count131072.C000032.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 8126465 5 2048 packet0.packed 282746462936 282748674018
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨8257536,8388608,278062634428,278064774738⟩
opaque packet1 : SegmentPacket 8257537 5 2048 278062634428 278064774738 := ⟨Manual.Count131072.C000033.packed,Manual.Count131072.C000033.count_checked,Manual.Count131072.C000033.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 8257537 5 2048 packet1.packed 278062634428 278064774738
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨8388608,8519680,273078100281,273080169640⟩
opaque packet2 : SegmentPacket 8388609 5 2048 273078100281 273080169640 := ⟨Manual.Count131072.C000034.packed,Manual.Count131072.C000034.count_checked,Manual.Count131072.C000034.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 8388609 5 2048 packet2.packed 273078100281 273080169640
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨8519680,8650752,270628334316,270630353969⟩
opaque packet3 : SegmentPacket 8519681 5 2048 270628334316 270630353969 := ⟨Manual.Count131072.C000035.packed,Manual.Count131072.C000035.count_checked,Manual.Count131072.C000035.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 8519681 5 2048 packet3.packed 270628334316 270630353969
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨8650752,8781824,266357487758,266359445660⟩
opaque packet4 : SegmentPacket 8650753 5 2048 266357487758 266359445660 := ⟨Manual.Count131072.C000036.packed,Manual.Count131072.C000036.count_checked,Manual.Count131072.C000036.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 8650753 5 2048 packet4.packed 266357487758 266359445660
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨8781824,8912896,259261399540,259263277087⟩
opaque packet5 : SegmentPacket 8781825 5 2048 259261399540 259263277087 := ⟨Manual.Count131072.C000037.packed,Manual.Count131072.C000037.count_checked,Manual.Count131072.C000037.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 8781825 5 2048 packet5.packed 259261399540 259263277087
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨8912896,9043968,255642813025,255644637473⟩
opaque packet6 : SegmentPacket 8912897 5 2048 255642813025 255644637473 := ⟨Manual.Count131072.C000038.packed,Manual.Count131072.C000038.count_checked,Manual.Count131072.C000038.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 8912897 5 2048 packet6.packed 255642813025 255644637473
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨9043968,9175040,252264714892,252266489357⟩
opaque packet7 : SegmentPacket 9043969 5 2048 252264714892 252266489357 := ⟨Manual.Count131072.C000039.packed,Manual.Count131072.C000039.count_checked,Manual.Count131072.C000039.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 9043969 5 2048 packet7.packed 252264714892 252266489357
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 8126464 9175040 2138041947176 2138057821942 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000004
