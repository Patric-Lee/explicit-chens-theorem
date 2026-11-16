import PlattSegmentPacket
import PlattCertificates.Count131072.C000024
import PlattCertificates.Count131072.C000025
import PlattCertificates.Count131072.C000026
import PlattCertificates.Count131072.C000027
import PlattCertificates.Count131072.C000028
import PlattCertificates.Count131072.C000029
import PlattCertificates.Count131072.C000030
import PlattCertificates.Count131072.C000031
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨7077888,7208960,325955735401,325958657966⟩
opaque packet0 : SegmentPacket 7077889 5 2048 325955735401 325958657966 := ⟨Manual.Count131072.C000024.packed,Manual.Count131072.C000024.count_checked,Manual.Count131072.C000024.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 7077889 5 2048 packet0.packed 325955735401 325958657966
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨7208960,7340032,320782014304,320784838764⟩
opaque packet1 : SegmentPacket 7208961 5 2048 320782014304 320784838764 := ⟨Manual.Count131072.C000025.packed,Manual.Count131072.C000025.count_checked,Manual.Count131072.C000025.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 7208961 5 2048 packet1.packed 320782014304 320784838764
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨7340032,7471104,314040810099,314043526335⟩
opaque packet2 : SegmentPacket 7340033 5 2048 314040810099 314043526335 := ⟨Manual.Count131072.C000026.packed,Manual.Count131072.C000026.count_checked,Manual.Count131072.C000026.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 7340033 5 2048 packet2.packed 314040810099 314043526335
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨7471104,7602176,308718290516,308720914279⟩
opaque packet3 : SegmentPacket 7471105 5 2048 308718290516 308720914279 := ⟨Manual.Count131072.C000027.packed,Manual.Count131072.C000027.count_checked,Manual.Count131072.C000027.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 7471105 5 2048 packet3.packed 308718290516 308720914279
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨7602176,7733248,304074860608,304077400865⟩
opaque packet4 : SegmentPacket 7602177 5 2048 304074860608 304077400865 := ⟨Manual.Count131072.C000028.packed,Manual.Count131072.C000028.count_checked,Manual.Count131072.C000028.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 7602177 5 2048 packet4.packed 304074860608 304077400865
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨7733248,7864320,298256172276,298258621923⟩
opaque packet5 : SegmentPacket 7733249 5 2048 298256172276 298258621923 := ⟨Manual.Count131072.C000029.packed,Manual.Count131072.C000029.count_checked,Manual.Count131072.C000029.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 7733249 5 2048 packet5.packed 298256172276 298258621923
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨7864320,7995392,292525947824,292528310938⟩
opaque packet6 : SegmentPacket 7864321 5 2048 292525947824 292528310938 := ⟨Manual.Count131072.C000030.packed,Manual.Count131072.C000030.count_checked,Manual.Count131072.C000030.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 7864321 5 2048 packet6.packed 292525947824 292528310938
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨7995392,8126464,286992776724,286995057391⟩
opaque packet7 : SegmentPacket 7995393 5 2048 286992776724 286995057391 := ⟨Manual.Count131072.C000031.packed,Manual.Count131072.C000031.count_checked,Manual.Count131072.C000031.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 7995393 5 2048 packet7.packed 286992776724 286995057391
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 7077888 8126464 2451346607752 2451367328461 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000003
