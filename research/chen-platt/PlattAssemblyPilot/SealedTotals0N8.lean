import PlattSegmentPacket
import PlattCertificates.Count131072.C000000
import PlattCertificates.Count131072.C000001
import PlattCertificates.Count131072.C000002
import PlattCertificates.Count131072.C000003
import PlattCertificates.Count131072.C000004
import PlattCertificates.Count131072.C000005
import PlattCertificates.Count131072.C000006
import PlattCertificates.Count131072.C000007
namespace ChenEffective.PlattWindow.AssemblyPilot.SealedTotals0N8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨4000000,4131072,598080220703,598084933579⟩
opaque packet0 : SegmentPacket 4000001 4 4096 598080220703 598084933579 :=
 ⟨Manual.Count131072.C000000.packed,Manual.Count131072.C000000.count_checked,Manual.Count131072.C000000.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 :=
 certifyIncrement 4000001 4 4096 packet0.packed 598080220703 598084933579
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨4131072,4194304,281556403798,281558570197⟩
opaque packet1 : SegmentPacket 4131073 4 1976 281556403798 281558570197 :=
 ⟨Manual.Count131072.C000001.packed,Manual.Count131072.C000001.count_checked,Manual.Count131072.C000001.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 :=
 certifyIncrement 4131073 4 1976 packet1.packed 281556403798 281558570197
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨4194304,4325376,563436548591,563445017565⟩
opaque packet2 : SegmentPacket 4194305 5 2048 563436548591 563445017565 :=
 ⟨Manual.Count131072.C000002.packed,Manual.Count131072.C000002.count_checked,Manual.Count131072.C000002.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 :=
 certifyIncrement 4194305 5 2048 packet2.packed 563436548591 563445017565
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨4325376,4456448,552068910285,552076959834⟩
opaque packet3 : SegmentPacket 4325377 5 2048 552068910285 552076959834 :=
 ⟨Manual.Count131072.C000003.packed,Manual.Count131072.C000003.count_checked,Manual.Count131072.C000003.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 :=
 certifyIncrement 4325377 5 2048 packet3.packed 552068910285 552076959834
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨4456448,4587520,532182173660,532189708963⟩
opaque packet4 : SegmentPacket 4456449 5 2048 532182173660 532189708963 :=
 ⟨Manual.Count131072.C000004.packed,Manual.Count131072.C000004.count_checked,Manual.Count131072.C000004.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 :=
 certifyIncrement 4456449 5 2048 packet4.packed 532182173660 532189708963
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨4587520,4718592,516808052010,516815163302⟩
opaque packet5 : SegmentPacket 4587521 5 2048 516808052010 516815163302 :=
 ⟨Manual.Count131072.C000005.packed,Manual.Count131072.C000005.count_checked,Manual.Count131072.C000005.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 :=
 certifyIncrement 4587521 5 2048 packet5.packed 516808052010 516815163302
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨4718592,4849664,500120888322,500127581581⟩
opaque packet6 : SegmentPacket 4718593 5 2048 500120888322 500127581581 :=
 ⟨Manual.Count131072.C000006.packed,Manual.Count131072.C000006.count_checked,Manual.Count131072.C000006.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 :=
 certifyIncrement 4718593 5 2048 packet6.packed 500120888322 500127581581
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨4849664,4980736,491480357459,491486759727⟩
opaque packet7 : SegmentPacket 4849665 5 2048 491480357459 491486759727 :=
 ⟨Manual.Count131072.C000007.packed,Manual.Count131072.C000007.count_checked,Manual.Count131072.C000007.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 :=
 certifyIncrement 4849665 5 2048 packet7.packed 491480357459 491486759727
 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows :=
 CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem summary_checked : checkIncrementSummary 4000000 4980736 4035733554828 4035784694748 rows = true := by
 decide +kernel
#print axioms all_certified
end ChenEffective.PlattWindow.AssemblyPilot.SealedTotals0N8
