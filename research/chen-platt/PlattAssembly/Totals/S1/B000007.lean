import PlattSegmentPacket
import PlattCertificates.Count131072.C000056
import PlattCertificates.Count131072.C000057
import PlattCertificates.Count131072.C000058
import PlattCertificates.Count131072.C000059
import PlattCertificates.Count131072.C000060
import PlattCertificates.Count131072.C000061
import PlattCertificates.Count131072.C000062
import PlattCertificates.Count131072.C000063
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨11272192,11403264,199755836557,199756966205⟩
opaque packet0 : SegmentPacket 11272193 5 2048 199755836557 199756966205 := ⟨Manual.Count131072.C000056.packed,Manual.Count131072.C000056.count_checked,Manual.Count131072.C000056.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 11272193 5 2048 packet0.packed 199755836557 199756966205
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨11403264,11534336,198010579988,198011687020⟩
opaque packet1 : SegmentPacket 11403265 5 2048 198010579988 198011687020 := ⟨Manual.Count131072.C000057.packed,Manual.Count131072.C000057.count_checked,Manual.Count131072.C000057.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 11403265 5 2048 packet1.packed 198010579988 198011687020
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨11534336,11665408,196869824691,196870912975⟩
opaque packet2 : SegmentPacket 11534337 5 2048 196869824691 196870912975 := ⟨Manual.Count131072.C000058.packed,Manual.Count131072.C000058.count_checked,Manual.Count131072.C000058.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 11534337 5 2048 packet2.packed 196869824691 196870912975
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨11665408,11796480,192793768972,192794822822⟩
opaque packet3 : SegmentPacket 11665409 5 2048 192793768972 192794822822 := ⟨Manual.Count131072.C000059.packed,Manual.Count131072.C000059.count_checked,Manual.Count131072.C000059.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 11665409 5 2048 packet3.packed 192793768972 192794822822
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨11796480,11927552,191468717037,191469752149⟩
opaque packet4 : SegmentPacket 11796481 5 2048 191468717037 191469752149 := ⟨Manual.Count131072.C000060.packed,Manual.Count131072.C000060.count_checked,Manual.Count131072.C000060.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 11796481 5 2048 packet4.packed 191468717037 191469752149
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨11927552,12058624,188557098949,188558107239⟩
opaque packet5 : SegmentPacket 11927553 5 2048 188557098949 188558107239 := ⟨Manual.Count131072.C000061.packed,Manual.Count131072.C000061.count_checked,Manual.Count131072.C000061.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 11927553 5 2048 packet5.packed 188557098949 188558107239
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨12058624,12189696,185868747198,185869730395⟩
opaque packet6 : SegmentPacket 12058625 5 2048 185868747198 185869730395 := ⟨Manual.Count131072.C000062.packed,Manual.Count131072.C000062.count_checked,Manual.Count131072.C000062.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 12058625 5 2048 packet6.packed 185868747198 185869730395
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨12189696,12320768,185576726021,185577697191⟩
opaque packet7 : SegmentPacket 12189697 5 2048 185576726021 185577697191 := ⟨Manual.Count131072.C000063.packed,Manual.Count131072.C000063.count_checked,Manual.Count131072.C000063.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 12189697 5 2048 packet7.packed 185576726021 185577697191
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 11272192 12320768 1538901299413 1538909675996 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000007
