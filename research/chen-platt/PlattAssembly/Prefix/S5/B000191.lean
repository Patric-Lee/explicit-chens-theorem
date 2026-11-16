import PlattAssemblyKernel
import PlattCertificates.Count131072.C046112
import PlattCertificates.Count131072.C046113
import PlattCertificates.Count131072.C046114
import PlattCertificates.Count131072.C046115
import PlattCertificates.Count131072.C046116
import PlattCertificates.Count131072.C046117
import PlattCertificates.Count131072.C046118
import PlattCertificates.Count131072.C046119
import PlattCertificates.Count131072.C046120
import PlattCertificates.Count131072.C046121
import PlattCertificates.Count131072.C046122
import PlattCertificates.Count131072.C046123
import PlattCertificates.Count131072.C046124
import PlattCertificates.Count131072.C046125
import PlattCertificates.Count131072.C046126
import PlattCertificates.Count131072.C046127
import PlattCertificates.Count131072.C046128
import PlattCertificates.Count131072.C046129
import PlattCertificates.Count131072.C046130
import PlattCertificates.Count131072.C046131
import PlattCertificates.Count131072.C046132
import PlattCertificates.Count131072.C046133
import PlattCertificates.Count131072.C046134
import PlattCertificates.Count131072.C046135
import PlattCertificates.Count131072.C046136
import PlattCertificates.Count131072.C046137
import PlattCertificates.Count131072.C046138
import PlattCertificates.Count131072.C046139
import PlattCertificates.Count131072.C046140
import PlattCertificates.Count131072.C046141
import PlattCertificates.Count131072.C046142
import PlattCertificates.Count131072.C046143
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000191
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46112 : List PrefixCut := [⟨64,267839077,267839230⟩]
theorem checked46112 : checkPrefixCuts (2^48) 6047924225 10 Manual.Count131072.C046112.packed 64 cuts46112 = true := by
 decide +kernel
def cuts46113 : List PrefixCut := [⟨12,52543258,52543283⟩,
⟨64,270020628,270020778⟩]
theorem checked46113 : checkPrefixCuts (2^48) 6048055297 10 Manual.Count131072.C046113.packed 64 cuts46113 = true := by
 decide +kernel
def pointBounds46113 : List (Nat × Nat × Nat) := [(6048079872,110647931212970,110648317758095)]
theorem point_links_checked46113 : (cuts46113.take 1).map (fun c => (6048055297-1+2*2^10*c.k,110647878669712+c.lower,110648265214812+c.upper)) = pointBounds46113 := by
 decide +kernel
def cuts46114 : List PrefixCut := [⟨41,173960566,173960668⟩,
⟨64,271876306,271876461⟩]
theorem checked46114 : checkPrefixCuts (2^48) 6048186369 10 Manual.Count131072.C046114.packed 64 cuts46114 = true := by
 decide +kernel
def pointBounds46114 : List (Nat × Nat × Nat) := [(6048270336,110648322650906,110648709196258)]
theorem point_links_checked46114 : (cuts46114.take 1).map (fun c => (6048186369-1+2*2^10*c.k,110648148690340+c.lower,110648535235590+c.upper)) = pointBounds46114 := by
 decide +kernel
def cuts46115 : List PrefixCut := [⟨64,272615009,272615162⟩]
theorem checked46115 : checkPrefixCuts (2^48) 6048317441 10 Manual.Count131072.C046115.packed 64 cuts46115 = true := by
 decide +kernel
def cuts46116 : List PrefixCut := [⟨6,25362482,25362496⟩,
⟨64,271259571,271259721⟩]
theorem checked46116 : checkPrefixCuts (2^48) 6048448513 10 Manual.Count131072.C046116.packed 64 cuts46116 = true := by
 decide +kernel
def pointBounds46116 : List (Nat × Nat × Nat) := [(6048460800,110648718544137,110649105089709)]
theorem point_links_checked46116 : (cuts46116.take 1).map (fun c => (6048448513-1+2*2^10*c.k,110648693181655+c.lower,110649079727213+c.upper)) = pointBounds46116 := by
 decide +kernel
def cuts46117 : List PrefixCut := [⟨35,144911309,144911396⟩,
⟨64,268973409,268973564⟩]
theorem checked46117 : checkPrefixCuts (2^48) 6048579585 10 Manual.Count131072.C046117.packed 64 cuts46117 = true := by
 decide +kernel
def pointBounds46117 : List (Nat × Nat × Nat) := [(6048651264,110649109352535,110649495898330)]
theorem point_links_checked46117 : (cuts46117.take 1).map (fun c => (6048579585-1+2*2^10*c.k,110648964441226+c.lower,110649350986934+c.upper)) = pointBounds46117 := by
 decide +kernel
def cuts46118 : List PrefixCut := [⟨64,270642837,270642997⟩]
theorem checked46118 : checkPrefixCuts (2^48) 6048710657 10 Manual.Count131072.C046118.packed 64 cuts46118 = true := by
 decide +kernel
def pointBounds46118 : List (Nat × Nat × Nat) := [(6048841728,110649504057472,110649890603495)]
theorem point_links_checked46118 : (cuts46118.take 1).map (fun c => (6048710657-1+2*2^10*c.k,110649233414635+c.lower,110649619960498+c.upper)) = pointBounds46118 := by
 decide +kernel
def cuts46119 : List PrefixCut := [⟨64,272079491,272079648⟩]
theorem checked46119 : checkPrefixCuts (2^48) 6048841729 10 Manual.Count131072.C046119.packed 64 cuts46119 = true := by
 decide +kernel
def cuts46120 : List PrefixCut := [⟨29,124800028,124800099⟩,
⟨64,270072759,270072917⟩]
theorem checked46120 : checkPrefixCuts (2^48) 6048972801 10 Manual.Count131072.C046120.packed 64 cuts46120 = true := by
 decide +kernel
def pointBounds46120 : List (Nat × Nat × Nat) := [(6049032192,110649900936991,110650287483242)]
theorem point_links_checked46120 : (cuts46120.take 1).map (fun c => (6048972801-1+2*2^10*c.k,110649776136963+c.lower,110650162683143+c.upper)) = pointBounds46120 := by
 decide +kernel
def cuts46121 : List PrefixCut := [⟨58,243358250,243358392⟩,
⟨64,268066056,268066212⟩]
theorem checked46121 : checkPrefixCuts (2^48) 6049103873 10 Manual.Count131072.C046121.packed 64 cuts46121 = true := by
 decide +kernel
def pointBounds46121 : List (Nat × Nat × Nat) := [(6049222656,110650289567972,110650676114452)]
theorem point_links_checked46121 : (cuts46121.take 1).map (fun c => (6049103873-1+2*2^10*c.k,110650046209722+c.lower,110650432756060+c.upper)) = pointBounds46121 := by
 decide +kernel
def cuts46122 : List PrefixCut := [⟨64,268758232,268758385⟩]
theorem checked46122 : checkPrefixCuts (2^48) 6049234945 10 Manual.Count131072.C046122.packed 64 cuts46122 = true := by
 decide +kernel
def cuts46123 : List PrefixCut := [⟨23,96874357,96874411⟩,
⟨64,270055176,270055337⟩]
theorem checked46123 : checkPrefixCuts (2^48) 6049366017 10 Manual.Count131072.C046123.packed 64 cuts46123 = true := by
 decide +kernel
def pointBounds46123 : List (Nat × Nat × Nat) := [(6049413120,110650679908367,110651066455068)]
theorem point_links_checked46123 : (cuts46123.take 1).map (fun c => (6049366017-1+2*2^10*c.k,110650583034010+c.lower,110650969580657+c.upper)) = pointBounds46123 := by
 decide +kernel
def cuts46124 : List PrefixCut := [⟨52,219008409,219008533⟩,
⟨64,269072246,269072400⟩]
theorem checked46124 : checkPrefixCuts (2^48) 6049497089 10 Manual.Count131072.C046124.packed 64 cuts46124 = true := by
 decide +kernel
def pointBounds46124 : List (Nat × Nat × Nat) := [(6049603584,110651072097595,110651458644527)]
theorem point_links_checked46124 : (cuts46124.take 1).map (fun c => (6049497089-1+2*2^10*c.k,110650853089186+c.lower,110651239635994+c.upper)) = pointBounds46124 := by
 decide +kernel
def cuts46125 : List PrefixCut := [⟨64,270880950,270881104⟩]
theorem checked46125 : checkPrefixCuts (2^48) 6049628161 10 Manual.Count131072.C046125.packed 64 cuts46125 = true := by
 decide +kernel
def cuts46126 : List PrefixCut := [⟨17,73418807,73418847⟩,
⟨64,271014691,271014842⟩]
theorem checked46126 : checkPrefixCuts (2^48) 6049759233 10 Manual.Count131072.C046126.packed 64 cuts46126 = true := by
 decide +kernel
def pointBounds46126 : List (Nat × Nat × Nat) := [(6049794048,110651466461189,110651853008345)]
theorem point_links_checked46126 : (cuts46126.take 1).map (fun c => (6049759233-1+2*2^10*c.k,110651393042382+c.lower,110651779589498+c.upper)) = pointBounds46126 := by
 decide +kernel
def cuts46127 : List PrefixCut := [⟨46,197313615,197313732⟩,
⟨64,273846836,273846997⟩]
theorem checked46127 : checkPrefixCuts (2^48) 6049890305 10 Manual.Count131072.C046127.packed 64 cuts46127 = true := by
 decide +kernel
def pointBounds46127 : List (Nat × Nat × Nat) := [(6049984512,110651861370688,110652247918072)]
theorem point_links_checked46127 : (cuts46127.take 1).map (fun c => (6049890305-1+2*2^10*c.k,110651664057073+c.lower,110652050604340+c.upper)) = pointBounds46127 := by
 decide +kernel
def cuts46128 : List PrefixCut := [⟨64,273887453,273887614⟩]
theorem checked46128 : checkPrefixCuts (2^48) 6050021377 10 Manual.Count131072.C046128.packed 64 cuts46128 = true := by
 decide +kernel
def cuts46129 : List PrefixCut := [⟨11,47407467,47407494⟩,
⟨64,273230181,273230340⟩]
theorem checked46129 : checkPrefixCuts (2^48) 6050152449 10 Manual.Count131072.C046129.packed 64 cuts46129 = true := by
 decide +kernel
def pointBounds46129 : List (Nat × Nat × Nat) := [(6050174976,110652259198829,110652645746445)]
theorem point_links_checked46129 : (cuts46129.take 1).map (fun c => (6050152449-1+2*2^10*c.k,110652211791362+c.lower,110652598338951+c.upper)) = pointBounds46129 := by
 decide +kernel
def cuts46130 : List PrefixCut := [⟨40,165898456,165898557⟩,
⟨64,263873320,263873480⟩]
theorem checked46130 : checkPrefixCuts (2^48) 6050283521 10 Manual.Count131072.C046130.packed 64 cuts46130 = true := by
 decide +kernel
def pointBounds46130 : List (Nat × Nat × Nat) := [(6050365440,110652650919999,110653037467848)]
theorem point_links_checked46130 : (cuts46130.take 1).map (fun c => (6050283521-1+2*2^10*c.k,110652485021543+c.lower,110652871569291+c.upper)) = pointBounds46130 := by
 decide +kernel
def cuts46131 : List PrefixCut := [⟨64,273916113,273916272⟩]
theorem checked46131 : checkPrefixCuts (2^48) 6050414593 10 Manual.Count131072.C046131.packed 64 cuts46131 = true := by
 decide +kernel
def cuts46132 : List PrefixCut := [⟨5,22283340,22283354⟩,
⟨64,272049432,272049589⟩]
theorem checked46132 : checkPrefixCuts (2^48) 6050545665 10 Manual.Count131072.C046132.packed 64 cuts46132 = true := by
 decide +kernel
def pointBounds46132 : List (Nat × Nat × Nat) := [(6050555904,110653045094316,110653431642397)]
theorem point_links_checked46132 : (cuts46132.take 1).map (fun c => (6050545665-1+2*2^10*c.k,110653022810976+c.lower,110653409359043+c.upper)) = pointBounds46132 := by
 decide +kernel
def cuts46133 : List PrefixCut := [⟨34,141465202,141465285⟩,
⟨64,270229239,270229394⟩]
theorem checked46133 : checkPrefixCuts (2^48) 6050676737 10 Manual.Count131072.C046133.packed 64 cuts46133 = true := by
 decide +kernel
def pointBounds46133 : List (Nat × Nat × Nat) := [(6050746368,110653436325610,110653822873917)]
theorem point_links_checked46133 : (cuts46133.take 1).map (fun c => (6050676737-1+2*2^10*c.k,110653294860408+c.lower,110653681408632+c.upper)) = pointBounds46133 := by
 decide +kernel
def cuts46134 : List PrefixCut := [⟨63,266548517,266548671⟩,
⟨64,271060721,271060877⟩]
theorem checked46134 : checkPrefixCuts (2^48) 6050807809 10 Manual.Count131072.C046134.packed 64 cuts46134 = true := by
 decide +kernel
def pointBounds46134 : List (Nat × Nat × Nat) := [(6050936832,110653831638164,110654218186697)]
theorem point_links_checked46134 : (cuts46134.take 1).map (fun c => (6050807809-1+2*2^10*c.k,110653565089647+c.lower,110653951638026+c.upper)) = pointBounds46134 := by
 decide +kernel
def cuts46135 : List PrefixCut := [⟨64,269240717,269240868⟩]
theorem checked46135 : checkPrefixCuts (2^48) 6050938881 10 Manual.Count131072.C046135.packed 64 cuts46135 = true := by
 decide +kernel
def cuts46136 : List PrefixCut := [⟨28,116151274,116151338⟩,
⟨64,270211693,270211844⟩]
theorem checked46136 : checkPrefixCuts (2^48) 6051069953 10 Manual.Count131072.C046136.packed 64 cuts46136 = true := by
 decide +kernel
def pointBounds46136 : List (Nat × Nat × Nat) := [(6051127296,110654221542359,110654608091109)]
theorem point_links_checked46136 : (cuts46136.take 1).map (fun c => (6051069953-1+2*2^10*c.k,110654105391085+c.lower,110654491939771+c.upper)) = pointBounds46136 := by
 decide +kernel
def cuts46137 : List PrefixCut := [⟨57,235831534,235831666⟩,
⟨64,267554484,267554633⟩]
theorem checked46137 : checkPrefixCuts (2^48) 6051201025 10 Manual.Count131072.C046137.packed 64 cuts46137 = true := by
 decide +kernel
def pointBounds46137 : List (Nat × Nat × Nat) := [(6051317760,110654611434312,110654997983281)]
theorem point_links_checked46137 : (cuts46137.take 1).map (fun c => (6051201025-1+2*2^10*c.k,110654375602778+c.lower,110654762151615+c.upper)) = pointBounds46137 := by
 decide +kernel
def cuts46138 : List PrefixCut := [⟨64,274153662,274153811⟩]
theorem checked46138 : checkPrefixCuts (2^48) 6051332097 10 Manual.Count131072.C046138.packed 64 cuts46138 = true := by
 decide +kernel
def cuts46139 : List PrefixCut := [⟨22,88049773,88049824⟩,
⟨64,266659124,266659276⟩]
theorem checked46139 : checkPrefixCuts (2^48) 6051463169 10 Manual.Count131072.C046139.packed 64 cuts46139 = true := by
 decide +kernel
def pointBounds46139 : List (Nat × Nat × Nat) := [(6051508224,110655005360697,110655391909883)]
theorem point_links_checked46139 : (cuts46139.take 1).map (fun c => (6051463169-1+2*2^10*c.k,110654917310924+c.lower,110655303860059+c.upper)) = pointBounds46139 := by
 decide +kernel
def cuts46140 : List PrefixCut := [⟨51,214048770,214048897⟩,
⟨64,269816196,269816354⟩]
theorem checked46140 : checkPrefixCuts (2^48) 6051594241 10 Manual.Count131072.C046140.packed 64 cuts46140 = true := by
 decide +kernel
def pointBounds46140 : List (Nat × Nat × Nat) := [(6051698688,110655398018818,110655784568232)]
theorem point_links_checked46140 : (cuts46140.take 1).map (fun c => (6051594241-1+2*2^10*c.k,110655183970048+c.lower,110655570519335+c.upper)) = pointBounds46140 := by
 decide +kernel
def cuts46141 : List PrefixCut := [⟨64,271345228,271345386⟩]
theorem checked46141 : checkPrefixCuts (2^48) 6051725313 10 Manual.Count131072.C046141.packed 64 cuts46141 = true := by
 decide +kernel
def cuts46142 : List PrefixCut := [⟨16,66928435,66928476⟩,
⟨64,271618395,271618553⟩]
theorem checked46142 : checkPrefixCuts (2^48) 6051856385 10 Manual.Count131072.C046142.packed 64 cuts46142 = true := by
 decide +kernel
def pointBounds46142 : List (Nat × Nat × Nat) := [(6051889152,110655792059907,110656178609551)]
theorem point_links_checked46142 : (cuts46142.take 1).map (fun c => (6051856385-1+2*2^10*c.k,110655725131472+c.lower,110656111681075+c.upper)) = pointBounds46142 := by
 decide +kernel
def cuts46143 : List PrefixCut := [⟨45,188082973,188083081⟩,
⟨64,271147403,271147562⟩]
theorem checked46143 : checkPrefixCuts (2^48) 6051987457 10 Manual.Count131072.C046143.packed 64 cuts46143 = true := by
 decide +kernel
def pointBounds46143 : List (Nat × Nat × Nat) := [(6052079616,110656184832840,110656571382709)]
theorem point_links_checked46143 : (cuts46143.take 1).map (fun c => (6051987457-1+2*2^10*c.k,110655996749867+c.lower,110656383299628+c.upper)) = pointBounds46143 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000191
