import PlattSegmentPacket
import PlattCertificates.Count131072.C000112
import PlattCertificates.Count131072.C000113
import PlattCertificates.Count131072.C000114
import PlattCertificates.Count131072.C000115
import PlattCertificates.Count131072.C000116
import PlattCertificates.Count131072.C000117
import PlattCertificates.Count131072.C000118
import PlattCertificates.Count131072.C000119
namespace ChenEffective.PlattWindow.Assembly.Totals.S1.B000014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def row0 : IncrementRow := ⟨18612224,18743296,118405259727,118406072201⟩
opaque packet0 : SegmentPacket 18612225 6 1024 118405259727 118406072201 := ⟨Manual.Count131072.C000112.packed,Manual.Count131072.C000112.count_checked,Manual.Count131072.C000112.arithmetic_checked⟩
theorem certified0 : IncrementCertified row0 := certifyIncrement 18612225 6 1024 packet0.packed 118405259727 118406072201
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet0.counts packet0.arithmetic
def row1 : IncrementRow := ⟨18743296,18874368,117144902086,117145700322⟩
opaque packet1 : SegmentPacket 18743297 6 1024 117144902086 117145700322 := ⟨Manual.Count131072.C000113.packed,Manual.Count131072.C000113.count_checked,Manual.Count131072.C000113.arithmetic_checked⟩
theorem certified1 : IncrementCertified row1 := certifyIncrement 18743297 6 1024 packet1.packed 117144902086 117145700322
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet1.counts packet1.arithmetic
def row2 : IncrementRow := ⟨18874368,19005440,115843710754,115844494661⟩
opaque packet2 : SegmentPacket 18874369 6 1024 115843710754 115844494661 := ⟨Manual.Count131072.C000114.packed,Manual.Count131072.C000114.count_checked,Manual.Count131072.C000114.arithmetic_checked⟩
theorem certified2 : IncrementCertified row2 := certifyIncrement 18874369 6 1024 packet2.packed 115843710754 115844494661
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet2.counts packet2.arithmetic
def row3 : IncrementRow := ⟨19005440,19136512,115254884653,115255659261⟩
opaque packet3 : SegmentPacket 19005441 6 1024 115254884653 115255659261 := ⟨Manual.Count131072.C000115.packed,Manual.Count131072.C000115.count_checked,Manual.Count131072.C000115.arithmetic_checked⟩
theorem certified3 : IncrementCertified row3 := certifyIncrement 19005441 6 1024 packet3.packed 115254884653 115255659261
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet3.counts packet3.arithmetic
def row4 : IncrementRow := ⟨19136512,19267584,114087169613,114087931142⟩
opaque packet4 : SegmentPacket 19136513 6 1024 114087169613 114087931142 := ⟨Manual.Count131072.C000116.packed,Manual.Count131072.C000116.count_checked,Manual.Count131072.C000116.arithmetic_checked⟩
theorem certified4 : IncrementCertified row4 := certifyIncrement 19136513 6 1024 packet4.packed 114087169613 114087931142
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet4.counts packet4.arithmetic
def row5 : IncrementRow := ⟨19267584,19398656,114172907117,114173664056⟩
opaque packet5 : SegmentPacket 19267585 6 1024 114172907117 114173664056 := ⟨Manual.Count131072.C000117.packed,Manual.Count131072.C000117.count_checked,Manual.Count131072.C000117.arithmetic_checked⟩
theorem certified5 : IncrementCertified row5 := certifyIncrement 19267585 6 1024 packet5.packed 114172907117 114173664056
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet5.counts packet5.arithmetic
def row6 : IncrementRow := ⟨19398656,19529728,112756147517,112756890102⟩
opaque packet6 : SegmentPacket 19398657 6 1024 112756147517 112756890102 := ⟨Manual.Count131072.C000118.packed,Manual.Count131072.C000118.count_checked,Manual.Count131072.C000118.arithmetic_checked⟩
theorem certified6 : IncrementCertified row6 := certifyIncrement 19398657 6 1024 packet6.packed 112756147517 112756890102
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet6.counts packet6.arithmetic
def row7 : IncrementRow := ⟨19529728,19660800,111294726286,111295454290⟩
opaque packet7 : SegmentPacket 19529729 6 1024 111294726286 111295454290 := ⟨Manual.Count131072.C000119.packed,Manual.Count131072.C000119.count_checked,Manual.Count131072.C000119.arithmetic_checked⟩
theorem certified7 : IncrementCertified row7 := certifyIncrement 19529729 6 1024 packet7.packed 111294726286 111295454290
 (by decide +kernel) (by decide +kernel) (by decide +kernel) packet7.counts packet7.arithmetic
def rows : List IncrementRow := [row0,row1,row2,row3,row4,row5,row6,row7]
theorem all_certified : CertifiedIncrements rows := CertifiedIncrements.cons certified0 (CertifiedIncrements.cons certified1 (CertifiedIncrements.cons certified2 (CertifiedIncrements.cons certified3 (CertifiedIncrements.cons certified4 (CertifiedIncrements.cons certified5 (CertifiedIncrements.cons certified6 (CertifiedIncrements.cons certified7 (CertifiedIncrements.nil))))))))
theorem checked : checkIncrementSummary 18612224 19660800 918959707753 918965866035 rows = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Totals.S1.B000014
