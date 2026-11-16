import PlattAssemblyKernel
import PlattCertificates.Count131072.C069120
import PlattCertificates.Count131072.C069121
import PlattCertificates.Count131072.C069122
import PlattCertificates.Count131072.C069123
import PlattCertificates.Count131072.C069124
import PlattCertificates.Count131072.C069125
import PlattCertificates.Count131072.C069126
import PlattCertificates.Count131072.C069127
import PlattCertificates.Count131072.C069128
import PlattCertificates.Count131072.C069129
import PlattCertificates.Count131072.C069130
import PlattCertificates.Count131072.C069131
import PlattCertificates.Count131072.C069132
import PlattCertificates.Count131072.C069133
import PlattCertificates.Count131072.C069134
import PlattCertificates.Count131072.C069135
import PlattCertificates.Count131072.C069136
import PlattCertificates.Count131072.C069137
import PlattCertificates.Count131072.C069138
import PlattCertificates.Count131072.C069139
import PlattCertificates.Count131072.C069140
import PlattCertificates.Count131072.C069141
import PlattCertificates.Count131072.C069142
import PlattCertificates.Count131072.C069143
import PlattCertificates.Count131072.C069144
import PlattCertificates.Count131072.C069145
import PlattCertificates.Count131072.C069146
import PlattCertificates.Count131072.C069147
import PlattCertificates.Count131072.C069148
import PlattCertificates.Count131072.C069149
import PlattCertificates.Count131072.C069150
import PlattCertificates.Count131072.C069151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000285
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69120 : List PrefixCut := [⟨20,55092213,55092244⟩,
⟨64,177263115,177263223⟩]
theorem checked69120 : checkPrefixCuts (2^48) 9063628801 10 Manual.Count131072.C069120.packed 64 cuts69120 = true := by
 decide +kernel
def pointBounds69120 : List (Nat × Nat × Nat) := [(9063669760,115658604312058,115658993726059)]
theorem point_links_checked69120 : (cuts69120.take 1).map (fun c => (9063628801-1+2*2^10*c.k,115658549219845+c.lower,115658938633815+c.upper)) = pointBounds69120 := by
 decide +kernel
def cuts69121 : List PrefixCut := [⟨64,179310181,179310286⟩]
theorem checked69121 : checkPrefixCuts (2^48) 9063759873 10 Manual.Count131072.C069121.packed 64 cuts69121 = true := by
 decide +kernel
def cuts69122 : List PrefixCut := [⟨31,87821909,87821961⟩,
⟨64,179090202,179090306⟩]
theorem checked69122 : checkPrefixCuts (2^48) 9063890945 10 Manual.Count131072.C069122.packed 64 cuts69122 = true := by
 decide +kernel
def pointBounds69122 : List (Nat × Nat × Nat) := [(9063954432,115658993615050,115659383029285)]
theorem point_links_checked69122 : (cuts69122.take 1).map (fun c => (9063890945-1+2*2^10*c.k,115658905793141+c.lower,115659295207324+c.upper)) = pointBounds69122 := by
 decide +kernel
def cuts69123 : List PrefixCut := [⟨64,175733783,175733885⟩]
theorem checked69123 : checkPrefixCuts (2^48) 9064022017 10 Manual.Count131072.C069123.packed 64 cuts69123 = true := by
 decide +kernel
def cuts69124 : List PrefixCut := [⟨42,115425814,115425881⟩,
⟨64,177346018,177346123⟩]
theorem checked69124 : checkPrefixCuts (2^48) 9064153089 10 Manual.Count131072.C069124.packed 64 cuts69124 = true := by
 decide +kernel
def pointBounds69124 : List (Nat × Nat × Nat) := [(9064239104,115659376042940,115659765457396)]
theorem point_links_checked69124 : (cuts69124.take 1).map (fun c => (9064153089-1+2*2^10*c.k,115659260617126+c.lower,115659650031515+c.upper)) = pointBounds69124 := by
 decide +kernel
def cuts69125 : List PrefixCut := [⟨64,177498736,177498838⟩]
theorem checked69125 : checkPrefixCuts (2^48) 9064284161 10 Manual.Count131072.C069125.packed 64 cuts69125 = true := by
 decide +kernel
def cuts69126 : List PrefixCut := [⟨53,147903291,147903380⟩,
⟨64,179483506,179483613⟩]
theorem checked69126 : checkPrefixCuts (2^48) 9064415233 10 Manual.Count131072.C069126.packed 64 cuts69126 = true := by
 decide +kernel
def pointBounds69126 : List (Nat × Nat × Nat) := [(9064523776,115659763365171,115660152779856)]
theorem point_links_checked69126 : (cuts69126.take 1).map (fun c => (9064415233-1+2*2^10*c.k,115659615461880+c.lower,115660004876476+c.upper)) = pointBounds69126 := by
 decide +kernel
def cuts69127 : List PrefixCut := [⟨64,178673563,178673669⟩]
theorem checked69127 : checkPrefixCuts (2^48) 9064546305 10 Manual.Count131072.C069127.packed 64 cuts69127 = true := by
 decide +kernel
def cuts69128 : List PrefixCut := [⟨64,178639925,178640025⟩]
theorem checked69128 : checkPrefixCuts (2^48) 9064677377 10 Manual.Count131072.C069128.packed 64 cuts69128 = true := by
 decide +kernel
def pointBounds69128 : List (Nat × Nat × Nat) := [(9064808448,115660152258874,115660541673783)]
theorem point_links_checked69128 : (cuts69128.take 1).map (fun c => (9064677377-1+2*2^10*c.k,115659973618949+c.lower,115660363033758+c.upper)) = pointBounds69128 := by
 decide +kernel
def cuts69129 : List PrefixCut := [⟨64,174476504,174476607⟩]
theorem checked69129 : checkPrefixCuts (2^48) 9064808449 10 Manual.Count131072.C069129.packed 64 cuts69129 = true := by
 decide +kernel
def cuts69130 : List PrefixCut := [⟨64,178852123,178852229⟩]
theorem checked69130 : checkPrefixCuts (2^48) 9064939521 10 Manual.Count131072.C069130.packed 64 cuts69130 = true := by
 decide +kernel
def cuts69131 : List PrefixCut := [⟨11,30615743,30615763⟩,
⟨64,176520757,176520866⟩]
theorem checked69131 : checkPrefixCuts (2^48) 9065070593 10 Manual.Count131072.C069131.packed 64 cuts69131 = true := by
 decide +kernel
def pointBounds69131 : List (Nat × Nat × Nat) := [(9065093120,115660536203244,115660925618382)]
theorem point_links_checked69131 : (cuts69131.take 1).map (fun c => (9065070593-1+2*2^10*c.k,115660505587501+c.lower,115660895002619+c.upper)) = pointBounds69131 := by
 decide +kernel
def cuts69132 : List PrefixCut := [⟨64,176456114,176456214⟩]
theorem checked69132 : checkPrefixCuts (2^48) 9065201665 10 Manual.Count131072.C069132.packed 64 cuts69132 = true := by
 decide +kernel
def cuts69133 : List PrefixCut := [⟨22,59335627,59335666⟩,
⟨64,174870044,174870148⟩]
theorem checked69133 : checkPrefixCuts (2^48) 9065332737 10 Manual.Count131072.C069133.packed 64 cuts69133 = true := by
 decide +kernel
def pointBounds69133 : List (Nat × Nat × Nat) := [(9065377792,115660917899999,115661307315365)]
theorem point_links_checked69133 : (cuts69133.take 1).map (fun c => (9065332737-1+2*2^10*c.k,115660858564372+c.lower,115661247979699+c.upper)) = pointBounds69133 := by
 decide +kernel
def cuts69134 : List PrefixCut := [⟨64,177196188,177196290⟩]
theorem checked69134 : checkPrefixCuts (2^48) 9065463809 10 Manual.Count131072.C069134.packed 64 cuts69134 = true := by
 decide +kernel
def cuts69135 : List PrefixCut := [⟨33,92866303,92866360⟩,
⟨64,177969842,177969952⟩]
theorem checked69135 : checkPrefixCuts (2^48) 9065594881 10 Manual.Count131072.C069135.packed 64 cuts69135 = true := by
 decide +kernel
def pointBounds69135 : List (Nat × Nat × Nat) := [(9065662464,115661303496907,115661692912497)]
theorem point_links_checked69135 : (cuts69135.take 1).map (fun c => (9065594881-1+2*2^10*c.k,115661210630604+c.lower,115661600046137+c.upper)) = pointBounds69135 := by
 decide +kernel
def cuts69136 : List PrefixCut := [⟨64,178619279,178619384⟩]
theorem checked69136 : checkPrefixCuts (2^48) 9065725953 10 Manual.Count131072.C069136.packed 64 cuts69136 = true := by
 decide +kernel
def cuts69137 : List PrefixCut := [⟨44,121396293,121396367⟩,
⟨64,178647731,178647842⟩]
theorem checked69137 : checkPrefixCuts (2^48) 9065857025 10 Manual.Count131072.C069137.packed 64 cuts69137 = true := by
 decide +kernel
def pointBounds69137 : List (Nat × Nat × Nat) := [(9065947136,115661688616018,115662078031840)]
theorem point_links_checked69137 : (cuts69137.take 1).map (fun c => (9065857025-1+2*2^10*c.k,115661567219725+c.lower,115661956635473+c.upper)) = pointBounds69137 := by
 decide +kernel
def cuts69138 : List PrefixCut := [⟨64,178024203,178024308⟩]
theorem checked69138 : checkPrefixCuts (2^48) 9065988097 10 Manual.Count131072.C069138.packed 64 cuts69138 = true := by
 decide +kernel
def cuts69139 : List PrefixCut := [⟨55,154146904,154146992⟩,
⟨64,179636068,179636167⟩]
theorem checked69139 : checkPrefixCuts (2^48) 9066119169 10 Manual.Count131072.C069139.packed 64 cuts69139 = true := by
 decide +kernel
def pointBounds69139 : List (Nat × Nat × Nat) := [(9066231808,115662078038563,115662467454615)]
theorem point_links_checked69139 : (cuts69139.take 1).map (fun c => (9066119169-1+2*2^10*c.k,115661923891659+c.lower,115662313307623+c.upper)) = pointBounds69139 := by
 decide +kernel
def cuts69140 : List PrefixCut := [⟨64,179664526,179664630⟩]
theorem checked69140 : checkPrefixCuts (2^48) 9066250241 10 Manual.Count131072.C069140.packed 64 cuts69140 = true := by
 decide +kernel
def cuts69141 : List PrefixCut := [⟨64,175408643,175408741⟩]
theorem checked69141 : checkPrefixCuts (2^48) 9066381313 10 Manual.Count131072.C069141.packed 64 cuts69141 = true := by
 decide +kernel
def cuts69142 : List PrefixCut := [⟨2,5681335,5681338⟩,
⟨64,176647930,176648040⟩]
theorem checked69142 : checkPrefixCuts (2^48) 9066512385 10 Manual.Count131072.C069142.packed 64 cuts69142 = true := by
 decide +kernel
def pointBounds69142 : List (Nat × Nat × Nat) := [(9066516480,115662464282231,115662853698499)]
theorem point_links_checked69142 : (cuts69142.take 1).map (fun c => (9066512385-1+2*2^10*c.k,115662458600896+c.lower,115662848017161+c.upper)) = pointBounds69142 := by
 decide +kernel
def cuts69143 : List PrefixCut := [⟨64,174751622,174751717⟩]
theorem checked69143 : checkPrefixCuts (2^48) 9066643457 10 Manual.Count131072.C069143.packed 64 cuts69143 = true := by
 decide +kernel
def cuts69144 : List PrefixCut := [⟨13,35359809,35359834⟩,
⟨64,180771698,180771813⟩]
theorem checked69144 : checkPrefixCuts (2^48) 9066774529 10 Manual.Count131072.C069144.packed 64 cuts69144 = true := by
 decide +kernel
def pointBounds69144 : List (Nat × Nat × Nat) := [(9066801152,115662845360257,115663234776752)]
theorem point_links_checked69144 : (cuts69144.take 1).map (fun c => (9066774529-1+2*2^10*c.k,115662810000448+c.lower,115663199416918+c.upper)) = pointBounds69144 := by
 decide +kernel
def cuts69145 : List PrefixCut := [⟨64,177105918,177106029⟩]
theorem checked69145 : checkPrefixCuts (2^48) 9066905601 10 Manual.Count131072.C069145.packed 64 cuts69145 = true := by
 decide +kernel
def cuts69146 : List PrefixCut := [⟨24,65377976,65378013⟩,
⟨64,175954734,175954838⟩]
theorem checked69146 : checkPrefixCuts (2^48) 9067036673 10 Manual.Count131072.C069146.packed 64 cuts69146 = true := by
 decide +kernel
def pointBounds69146 : List (Nat × Nat × Nat) := [(9067085824,115663233256040,115663622672773)]
theorem point_links_checked69146 : (cuts69146.take 1).map (fun c => (9067036673-1+2*2^10*c.k,115663167878064+c.lower,115663557294760+c.upper)) = pointBounds69146 := by
 decide +kernel
def cuts69147 : List PrefixCut := [⟨64,178094174,178094275⟩]
theorem checked69147 : checkPrefixCuts (2^48) 9067167745 10 Manual.Count131072.C069147.packed 64 cuts69147 = true := by
 decide +kernel
def cuts69148 : List PrefixCut := [⟨35,96480831,96480885⟩,
⟨64,175577153,175577251⟩]
theorem checked69148 : checkPrefixCuts (2^48) 9067298817 10 Manual.Count131072.C069148.packed 64 cuts69148 = true := by
 decide +kernel
def pointBounds69148 : List (Nat × Nat × Nat) := [(9067370496,115663618407803,115664007824758)]
theorem point_links_checked69148 : (cuts69148.take 1).map (fun c => (9067298817-1+2*2^10*c.k,115663521926972+c.lower,115663911343873+c.upper)) = pointBounds69148 := by
 decide +kernel
def cuts69149 : List PrefixCut := [⟨64,176536930,176537035⟩]
theorem checked69149 : checkPrefixCuts (2^48) 9067429889 10 Manual.Count131072.C069149.packed 64 cuts69149 = true := by
 decide +kernel
def cuts69150 : List PrefixCut := [⟨46,129972029,129972101⟩,
⟨64,178552097,178552201⟩]
theorem checked69150 : checkPrefixCuts (2^48) 9067560961 10 Manual.Count131072.C069150.packed 64 cuts69150 = true := by
 decide +kernel
def pointBounds69150 : List (Nat × Nat × Nat) := [(9067655168,115664004013084,115664393430260)]
theorem point_links_checked69150 : (cuts69150.take 1).map (fun c => (9067560961-1+2*2^10*c.k,115663874041055+c.lower,115664263458159+c.upper)) = pointBounds69150 := by
 decide +kernel
def cuts69151 : List PrefixCut := [⟨64,178083892,178083994⟩]
theorem checked69151 : checkPrefixCuts (2^48) 9067692033 10 Manual.Count131072.C069151.packed 64 cuts69151 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000285
