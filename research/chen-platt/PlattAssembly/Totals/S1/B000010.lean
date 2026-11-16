import PlattSegmentPacket
import PlattCertificates.Count131072.C000080
import PlattCertificates.Count131072.C000081
import PlattCertificates.Count131072.C000082
import PlattCertificates.Count131072.C000083
import PlattCertificates.Count131072.C000084
import PlattCertificates.Count131072.C000085
import PlattCertificates.Count131072.C000086
import PlattCertificates.Count131072.C000087
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨14417920,14548992,153628617742,153629298684⟩
opaque packet0 : SegmentPacket 14417921 5 2048 153628617742 153629298684 := ⟨Manual.Count131072.C000080.packed,Manual.Count131072.C000080.count_checked,Manual.Count131072.C000080.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 14417921 5 2048 packet0.packed 153628617742 153629298684
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨14548992,14680064,152811129681,152811800948⟩
opaque packet1 : SegmentPacket 14548993 5 2048 152811129681 152811800948 := ⟨Manual.Count131072.C000081.packed,Manual.Count131072.C000081.count_checked,Manual.Count131072.C000081.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 14548993 5 2048 packet1.packed 152811129681 152811800948
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨14680064,14811136,152367170545,152367833930⟩
opaque packet2 : SegmentPacket 14680065 5 2048 152367170545 152367833930 := ⟨Manual.Count131072.C000082.packed,Manual.Count131072.C000082.count_checked,Manual.Count131072.C000082.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 14680065 5 2048 packet2.packed 152367170545 152367833930
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨14811136,14942208,149417210345,149417855169⟩
opaque packet3 : SegmentPacket 14811137 5 2048 149417210345 149417855169 := ⟨Manual.Count131072.C000083.packed,Manual.Count131072.C000083.count_checked,Manual.Count131072.C000083.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 14811137 5 2048 packet3.packed 149417210345 149417855169
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨14942208,15073280,148149114583,148149748405⟩
opaque packet4 : SegmentPacket 14942209 5 2048 148149114583 148149748405 := ⟨Manual.Count131072.C000084.packed,Manual.Count131072.C000084.count_checked,Manual.Count131072.C000084.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 14942209 5 2048 packet4.packed 148149114583 148149748405
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨15073280,15204352,146887120259,146887743274⟩
opaque packet5 : SegmentPacket 15073281 5 2048 146887120259 146887743274 := ⟨Manual.Count131072.C000085.packed,Manual.Count131072.C000085.count_checked,Manual.Count131072.C000085.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 15073281 5 2048 packet5.packed 146887120259 146887743274
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨15204352,15335424,146639639373,146640256036⟩
opaque packet6 : SegmentPacket 15204353 5 2048 146639639373 146640256036 := ⟨Manual.Count131072.C000086.packed,Manual.Count131072.C000086.count_checked,Manual.Count131072.C000086.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 15204353 5 2048 packet6.packed 146639639373 146640256036
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨15335424,15466496,143580039349,143580638082⟩
opaque packet7 : SegmentPacket 15335425 5 2048 143580039349 143580638082 := ⟨Manual.Count131072.C000087.packed,Manual.Count131072.C000087.count_checked,Manual.Count131072.C000087.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 15335425 5 2048 packet7.packed 143580039349 143580638082
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 14417920 15466496 1193480041877 1193485174528 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000010
