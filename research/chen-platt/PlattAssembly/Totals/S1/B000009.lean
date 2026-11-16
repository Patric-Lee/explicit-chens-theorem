import PlattSegmentPacket
import PlattCertificates.Count131072.C000072
import PlattCertificates.Count131072.C000073
import PlattCertificates.Count131072.C000074
import PlattCertificates.Count131072.C000075
import PlattCertificates.Count131072.C000076
import PlattCertificates.Count131072.C000077
import PlattCertificates.Count131072.C000078
import PlattCertificates.Count131072.C000079
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨13369344,13500416,166079689886,166080483109⟩
opaque packet0 : SegmentPacket 13369345 5 2048 166079689886 166080483109 := ⟨Manual.Count131072.C000072.packed,Manual.Count131072.C000072.count_checked,Manual.Count131072.C000072.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 13369345 5 2048 packet0.packed 166079689886 166080483109
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨13500416,13631488,165572239960,165573023132⟩
opaque packet1 : SegmentPacket 13500417 5 2048 165572239960 165573023132 := ⟨Manual.Count131072.C000073.packed,Manual.Count131072.C000073.count_checked,Manual.Count131072.C000073.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 13500417 5 2048 packet1.packed 165572239960 165573023132
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨13631488,13762560,164321940809,164322710681⟩
opaque packet2 : SegmentPacket 13631489 5 2048 164321940809 164322710681 := ⟨Manual.Count131072.C000074.packed,Manual.Count131072.C000074.count_checked,Manual.Count131072.C000074.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 13631489 5 2048 packet2.packed 164321940809 164322710681
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨13762560,13893632,163046984336,163047741013⟩
opaque packet3 : SegmentPacket 13762561 5 2048 163046984336 163047741013 := ⟨Manual.Count131072.C000075.packed,Manual.Count131072.C000075.count_checked,Manual.Count131072.C000075.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 13762561 5 2048 packet3.packed 163046984336 163047741013
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨13893632,14024704,159785466565,159786201242⟩
opaque packet4 : SegmentPacket 13893633 5 2048 159785466565 159786201242 := ⟨Manual.Count131072.C000076.packed,Manual.Count131072.C000076.count_checked,Manual.Count131072.C000076.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 13893633 5 2048 packet4.packed 159785466565 159786201242
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨14024704,14155776,159413342630,159414068784⟩
opaque packet5 : SegmentPacket 14024705 5 2048 159413342630 159414068784 := ⟨Manual.Count131072.C000077.packed,Manual.Count131072.C000077.count_checked,Manual.Count131072.C000077.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 14024705 5 2048 packet5.packed 159413342630 159414068784
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨14155776,14286848,157228128682,157228838309⟩
opaque packet6 : SegmentPacket 14155777 5 2048 157228128682 157228838309 := ⟨Manual.Count131072.C000078.packed,Manual.Count131072.C000078.count_checked,Manual.Count131072.C000078.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 14155777 5 2048 packet6.packed 157228128682 157228838309
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨14286848,14417920,157207938489,157208641575⟩
opaque packet7 : SegmentPacket 14286849 5 2048 157207938489 157208641575 := ⟨Manual.Count131072.C000079.packed,Manual.Count131072.C000079.count_checked,Manual.Count131072.C000079.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 14286849 5 2048 packet7.packed 157207938489 157208641575
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 13369344 14417920 1292655731357 1292661707845 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000009
