import PlattSegmentPacket
import PlattCertificates.Count131072.C000016
import PlattCertificates.Count131072.C000017
import PlattCertificates.Count131072.C000018
import PlattCertificates.Count131072.C000019
import PlattCertificates.Count131072.C000020
import PlattCertificates.Count131072.C000021
import PlattCertificates.Count131072.C000022
import PlattCertificates.Count131072.C000023
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨6029312,6160384,385520819735,385524870086⟩
opaque packet0 : SegmentPacket 6029313 5 2048 385520819735 385524870086 := ⟨Manual.Count131072.C000016.packed,Manual.Count131072.C000016.count_checked,Manual.Count131072.C000016.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 6029313 5 2048 packet0.packed 385520819735 385524870086
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨6160384,6291456,378995390021,378999288169⟩
opaque packet1 : SegmentPacket 6160385 5 2048 378995390021 378999288169 := ⟨Manual.Count131072.C000017.packed,Manual.Count131072.C000017.count_checked,Manual.Count131072.C000017.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 6160385 5 2048 packet1.packed 378995390021 378999288169
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨6291456,6422528,369178001091,369181720409⟩
opaque packet2 : SegmentPacket 6291457 5 2048 369178001091 369181720409 := ⟨Manual.Count131072.C000018.packed,Manual.Count131072.C000018.count_checked,Manual.Count131072.C000018.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 6291457 5 2048 packet2.packed 369178001091 369181720409
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨6422528,6553600,361953766917,361957339579⟩
opaque packet3 : SegmentPacket 6422529 5 2048 361953766917 361957339579 := ⟨Manual.Count131072.C000019.packed,Manual.Count131072.C000019.count_checked,Manual.Count131072.C000019.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 6422529 5 2048 packet3.packed 361953766917 361957339579
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨6553600,6684672,354469345955,354472775772⟩
opaque packet4 : SegmentPacket 6553601 5 2048 354469345955 354472775772 := ⟨Manual.Count131072.C000020.packed,Manual.Count131072.C000020.count_checked,Manual.Count131072.C000020.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 6553601 5 2048 packet4.packed 354469345955 354472775772
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨6684672,6815744,348787927287,348791236606⟩
opaque packet5 : SegmentPacket 6684673 5 2048 348787927287 348791236606 := ⟨Manual.Count131072.C000021.packed,Manual.Count131072.C000021.count_checked,Manual.Count131072.C000021.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 6684673 5 2048 packet5.packed 348787927287 348791236606
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨6815744,6946816,342225484520,342228669796⟩
opaque packet6 : SegmentPacket 6815745 5 2048 342225484520 342228669796 := ⟨Manual.Count131072.C000022.packed,Manual.Count131072.C000022.count_checked,Manual.Count131072.C000022.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 6815745 5 2048 packet6.packed 342225484520 342228669796
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨6946816,7077888,335904969025,335908037054⟩
opaque packet7 : SegmentPacket 6946817 5 2048 335904969025 335908037054 := ⟨Manual.Count131072.C000023.packed,Manual.Count131072.C000023.count_checked,Manual.Count131072.C000023.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 6946817 5 2048 packet7.packed 335904969025 335908037054
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 6029312 7077888 2877035704551 2877063937471 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000002
