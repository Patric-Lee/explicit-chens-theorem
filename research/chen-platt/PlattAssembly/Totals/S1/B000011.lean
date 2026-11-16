import PlattSegmentPacket
import PlattCertificates.Count131072.C000088
import PlattCertificates.Count131072.C000089
import PlattCertificates.Count131072.C000090
import PlattCertificates.Count131072.C000091
import PlattCertificates.Count131072.C000092
import PlattCertificates.Count131072.C000093
import PlattCertificates.Count131072.C000094
import PlattCertificates.Count131072.C000095
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨15466496,15597568,144976783557,144977382976⟩
opaque packet0 : SegmentPacket 15466497 5 2048 144976783557 144977382976 := ⟨Manual.Count131072.C000088.packed,Manual.Count131072.C000088.count_checked,Manual.Count131072.C000088.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 15466497 5 2048 packet0.packed 144976783557 144977382976
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨15597568,15728640,141842128640,141842710259⟩
opaque packet1 : SegmentPacket 15597569 5 2048 141842128640 141842710259 := ⟨Manual.Count131072.C000089.packed,Manual.Count131072.C000089.count_checked,Manual.Count131072.C000089.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 15597569 5 2048 packet1.packed 141842128640 141842710259
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨15728640,15859712,141285789900,141286364427⟩
opaque packet2 : SegmentPacket 15728641 5 2048 141285789900 141286364427 := ⟨Manual.Count131072.C000090.packed,Manual.Count131072.C000090.count_checked,Manual.Count131072.C000090.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 15728641 5 2048 packet2.packed 141285789900 141286364427
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨15859712,15990784,139737653444,139738217089⟩
opaque packet3 : SegmentPacket 15859713 5 2048 139737653444 139738217089 := ⟨Manual.Count131072.C000091.packed,Manual.Count131072.C000091.count_checked,Manual.Count131072.C000091.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 15859713 5 2048 packet3.packed 139737653444 139738217089
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨15990784,16121856,137981883079,137982435126⟩
opaque packet4 : SegmentPacket 15990785 5 2048 137981883079 137982435126 := ⟨Manual.Count131072.C000092.packed,Manual.Count131072.C000092.count_checked,Manual.Count131072.C000092.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 15990785 5 2048 packet4.packed 137981883079 137982435126
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨16121856,16252928,137125266435,137125810648⟩
opaque packet5 : SegmentPacket 16121857 5 2048 137125266435 137125810648 := ⟨Manual.Count131072.C000093.packed,Manual.Count131072.C000093.count_checked,Manual.Count131072.C000093.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 16121857 5 2048 packet5.packed 137125266435 137125810648
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨16252928,16384000,135371889107,135372422135⟩
opaque packet6 : SegmentPacket 16252929 5 2048 135371889107 135372422135 := ⟨Manual.Count131072.C000094.packed,Manual.Count131072.C000094.count_checked,Manual.Count131072.C000094.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 16252929 5 2048 packet6.packed 135371889107 135372422135
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨16384000,16515072,135677046766,135677576694⟩
opaque packet7 : SegmentPacket 16384001 5 2048 135677046766 135677576694 := ⟨Manual.Count131072.C000095.packed,Manual.Count131072.C000095.count_checked,Manual.Count131072.C000095.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 16384001 5 2048 packet7.packed 135677046766 135677576694
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 15466496 16515072 1113998440928 1114002919354 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000011
