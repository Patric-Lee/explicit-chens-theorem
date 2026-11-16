import PlattAssemblyKernel
import PlattCertificates.Count131072.C058096
import PlattCertificates.Count131072.C058097
import PlattCertificates.Count131072.C058098
import PlattCertificates.Count131072.C058099
import PlattCertificates.Count131072.C058100
import PlattCertificates.Count131072.C058101
import PlattCertificates.Count131072.C058102
import PlattCertificates.Count131072.C058103
import PlattCertificates.Count131072.C058104
import PlattCertificates.Count131072.C058105
import PlattCertificates.Count131072.C058106
import PlattCertificates.Count131072.C058107
import PlattCertificates.Count131072.C058108
import PlattCertificates.Count131072.C058109
import PlattCertificates.Count131072.C058110
import PlattCertificates.Count131072.C058111
import PlattCertificates.Count131072.C058112
import PlattCertificates.Count131072.C058113
import PlattCertificates.Count131072.C058114
import PlattCertificates.Count131072.C058115
import PlattCertificates.Count131072.C058116
import PlattCertificates.Count131072.C058117
import PlattCertificates.Count131072.C058118
import PlattCertificates.Count131072.C058119
import PlattCertificates.Count131072.C058120
import PlattCertificates.Count131072.C058121
import PlattCertificates.Count131072.C058122
import PlattCertificates.Count131072.C058123
import PlattCertificates.Count131072.C058124
import PlattCertificates.Count131072.C058125
import PlattCertificates.Count131072.C058126
import PlattCertificates.Count131072.C058127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000253
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58096 : List PrefixCut := [⟨64,213394273,213394396⟩]
theorem checked58096 : checkPrefixCuts (2^48) 7618691073 10 Manual.Count131072.C058096.packed 64 cuts58096 = true := by
 decide +kernel
def cuts58097 : List PrefixCut := [⟨17,57596612,57596647⟩,
⟨64,214092543,214092667⟩]
theorem checked58097 : checkPrefixCuts (2^48) 7618822145 10 Manual.Count131072.C058097.packed 64 cuts58097 = true := by
 decide +kernel
def pointBounds58097 : List (Nat × Nat × Nat) := [(7618856960,113518619048205,113519007228282)]
theorem point_links_checked58097 : (cuts58097.take 1).map (fun c => (7618822145-1+2*2^10*c.k,113518561451593+c.lower,113518949631635+c.upper)) = pointBounds58097 := by
 decide +kernel
def cuts58098 : List PrefixCut := [⟨64,212648051,212648174⟩]
theorem checked58098 : checkPrefixCuts (2^48) 7618953217 10 Manual.Count131072.C058098.packed 64 cuts58098 = true := by
 decide +kernel
def cuts58099 : List PrefixCut := [⟨6,20540517,20540528⟩,
⟨64,210834187,210834312⟩]
theorem checked58099 : checkPrefixCuts (2^48) 7619084289 10 Manual.Count131072.C058099.packed 64 cuts58099 = true := by
 decide +kernel
def pointBounds58099 : List (Nat × Nat × Nat) := [(7619096576,113519008732704,113519396913004)]
theorem point_links_checked58099 : (cuts58099.take 1).map (fun c => (7619084289-1+2*2^10*c.k,113518988192187+c.lower,113519376372476+c.upper)) = pointBounds58099 := by
 decide +kernel
def cuts58100 : List PrefixCut := [⟨59,195499567,195499684⟩,
⟨64,212677669,212677796⟩]
theorem checked58100 : checkPrefixCuts (2^48) 7619215361 10 Manual.Count131072.C058100.packed 64 cuts58100 = true := by
 decide +kernel
def pointBounds58100 : List (Nat × Nat × Nat) := [(7619336192,113519394525941,113519782706472)]
theorem point_links_checked58100 : (cuts58100.take 1).map (fun c => (7619215361-1+2*2^10*c.k,113519199026374+c.lower,113519587206788+c.upper)) = pointBounds58100 := by
 decide +kernel
def cuts58101 : List PrefixCut := [⟨64,216035720,216035847⟩]
theorem checked58101 : checkPrefixCuts (2^48) 7619346433 10 Manual.Count131072.C058101.packed 64 cuts58101 = true := by
 decide +kernel
def cuts58102 : List PrefixCut := [⟨48,156224574,156224668⟩,
⟨64,210306109,210306233⟩]
theorem checked58102 : checkPrefixCuts (2^48) 7619477505 10 Manual.Count131072.C058102.packed 64 cuts58102 = true := by
 decide +kernel
def pointBounds58102 : List (Nat × Nat × Nat) := [(7619575808,113519783964337,113520172145099)]
theorem point_links_checked58102 : (cuts58102.take 1).map (fun c => (7619477505-1+2*2^10*c.k,113519627739763+c.lower,113520015920431+c.upper)) = pointBounds58102 := by
 decide +kernel
def cuts58103 : List PrefixCut := [⟨64,217468961,217469082⟩]
theorem checked58103 : checkPrefixCuts (2^48) 7619608577 10 Manual.Count131072.C058103.packed 64 cuts58103 = true := by
 decide +kernel
def cuts58104 : List PrefixCut := [⟨37,121754374,121754444⟩,
⟨64,212256697,212256819⟩]
theorem checked58104 : checkPrefixCuts (2^48) 7619739649 10 Manual.Count131072.C058104.packed 64 cuts58104 = true := by
 decide +kernel
def pointBounds58104 : List (Nat × Nat × Nat) := [(7619815424,113520177269207,113520565450190)]
theorem point_links_checked58104 : (cuts58104.take 1).map (fun c => (7619739649-1+2*2^10*c.k,113520055514833+c.lower,113520443695746+c.upper)) = pointBounds58104 := by
 decide +kernel
def cuts58105 : List PrefixCut := [⟨64,212807132,212807252⟩]
theorem checked58105 : checkPrefixCuts (2^48) 7619870721 10 Manual.Count131072.C058105.packed 64 cuts58105 = true := by
 decide +kernel
def cuts58106 : List PrefixCut := [⟨26,89576650,89576700⟩,
⟨64,214798191,214798313⟩]
theorem checked58106 : checkPrefixCuts (2^48) 7620001793 10 Manual.Count131072.C058106.packed 64 cuts58106 = true := by
 decide +kernel
def pointBounds58106 : List (Nat × Nat × Nat) := [(7620055040,113520570155312,113520958336517)]
theorem point_links_checked58106 : (cuts58106.take 1).map (fun c => (7620001793-1+2*2^10*c.k,113520480578662+c.lower,113520868759817+c.upper)) = pointBounds58106 := by
 decide +kernel
def cuts58107 : List PrefixCut := [⟨64,214462033,214462158⟩]
theorem checked58107 : checkPrefixCuts (2^48) 7620132865 10 Manual.Count131072.C058107.packed 64 cuts58107 = true := by
 decide +kernel
def cuts58108 : List PrefixCut := [⟨15,49570269,49570297⟩,
⟨64,215714197,215714322⟩]
theorem checked58108 : checkPrefixCuts (2^48) 7620263937 10 Manual.Count131072.C058108.packed 64 cuts58108 = true := by
 decide +kernel
def pointBounds58108 : List (Nat × Nat × Nat) := [(7620294656,113520959409155,113521347590585)]
theorem point_links_checked58108 : (cuts58108.take 1).map (fun c => (7620263937-1+2*2^10*c.k,113520909838886+c.lower,113521298020288+c.upper)) = pointBounds58108 := by
 decide +kernel
def cuts58109 : List PrefixCut := [⟨64,212127639,212127764⟩]
theorem checked58109 : checkPrefixCuts (2^48) 7620395009 10 Manual.Count131072.C058109.packed 64 cuts58109 = true := by
 decide +kernel
def cuts58110 : List PrefixCut := [⟨4,12927738,12927744⟩,
⟨64,209870890,209871012⟩]
theorem checked58110 : checkPrefixCuts (2^48) 7620526081 10 Manual.Count131072.C058110.packed 64 cuts58110 = true := by
 decide +kernel
def pointBounds58110 : List (Nat × Nat × Nat) := [(7620534272,113521350608460,113521738790118)]
theorem point_links_checked58110 : (cuts58110.take 1).map (fun c => (7620526081-1+2*2^10*c.k,113521337680722+c.lower,113521725862374+c.upper)) = pointBounds58110 := by
 decide +kernel
def cuts58111 : List PrefixCut := [⟨57,189663757,189663866⟩,
⟨64,213671620,213671743⟩]
theorem checked58111 : checkPrefixCuts (2^48) 7620657153 10 Manual.Count131072.C058111.packed 64 cuts58111 = true := by
 decide +kernel
def pointBounds58111 : List (Nat × Nat × Nat) := [(7620773888,113521737215369,113522125397252)]
theorem point_links_checked58111 : (cuts58111.take 1).map (fun c => (7620657153-1+2*2^10*c.k,113521547551612+c.lower,113521935733386+c.upper)) = pointBounds58111 := by
 decide +kernel
def cuts58112 : List PrefixCut := [⟨64,212966193,212966308⟩]
theorem checked58112 : checkPrefixCuts (2^48) 7620788225 10 Manual.Count131072.C058112.packed 64 cuts58112 = true := by
 decide +kernel
def cuts58113 : List PrefixCut := [⟨46,154533017,154533105⟩,
⟨64,214956979,214957100⟩]
theorem checked58113 : checkPrefixCuts (2^48) 7620919297 10 Manual.Count131072.C058113.packed 64 cuts58113 = true := by
 decide +kernel
def pointBounds58113 : List (Nat × Nat × Nat) := [(7621013504,113522128722442,113522516904542)]
theorem point_links_checked58113 : (cuts58113.take 1).map (fun c => (7620919297-1+2*2^10*c.k,113521974189425+c.lower,113522362371437+c.upper)) = pointBounds58113 := by
 decide +kernel
def cuts58114 : List PrefixCut := [⟨64,211887800,211887923⟩]
theorem checked58114 : checkPrefixCuts (2^48) 7621050369 10 Manual.Count131072.C058114.packed 64 cuts58114 = true := by
 decide +kernel
def cuts58115 : List PrefixCut := [⟨35,116117549,116117617⟩,
⟨64,211588697,211588821⟩]
theorem checked58115 : checkPrefixCuts (2^48) 7621181441 10 Manual.Count131072.C058115.packed 64 cuts58115 = true := by
 decide +kernel
def pointBounds58115 : List (Nat × Nat × Nat) := [(7621253120,113522517151753,113522905334077)]
theorem point_links_checked58115 : (cuts58115.take 1).map (fun c => (7621181441-1+2*2^10*c.k,113522401034204+c.lower,113522789216460+c.upper)) = pointBounds58115 := by
 decide +kernel
def cuts58116 : List PrefixCut := [⟨64,214798155,214798275⟩]
theorem checked58116 : checkPrefixCuts (2^48) 7621312513 10 Manual.Count131072.C058116.packed 64 cuts58116 = true := by
 decide +kernel
def cuts58117 : List PrefixCut := [⟨24,79846654,79846701⟩,
⟨64,211876875,211876997⟩]
theorem checked58117 : checkPrefixCuts (2^48) 7621443585 10 Manual.Count131072.C058117.packed 64 cuts58117 = true := by
 decide +kernel
def pointBounds58117 : List (Nat × Nat × Nat) := [(7621492736,113522907267710,113523295450257)]
theorem point_links_checked58117 : (cuts58117.take 1).map (fun c => (7621443585-1+2*2^10*c.k,113522827421056+c.lower,113523215603556+c.upper)) = pointBounds58117 := by
 decide +kernel
def cuts58118 : List PrefixCut := [⟨64,212981161,212981285⟩]
theorem checked58118 : checkPrefixCuts (2^48) 7621574657 10 Manual.Count131072.C058118.packed 64 cuts58118 = true := by
 decide +kernel
def cuts58119 : List PrefixCut := [⟨13,43873590,43873614⟩,
⟨64,215525688,215525808⟩]
theorem checked58119 : checkPrefixCuts (2^48) 7621705729 10 Manual.Count131072.C058119.packed 64 cuts58119 = true := by
 decide +kernel
def pointBounds58119 : List (Nat × Nat × Nat) := [(7621732352,113523296152682,113523684335452)]
theorem point_links_checked58119 : (cuts58119.take 1).map (fun c => (7621705729-1+2*2^10*c.k,113523252279092+c.lower,113523640461838+c.upper)) = pointBounds58119 := by
 decide +kernel
def cuts58120 : List PrefixCut := [⟨64,211385855,211385977⟩]
theorem checked58120 : checkPrefixCuts (2^48) 7621836801 10 Manual.Count131072.C058120.packed 64 cuts58120 = true := by
 decide +kernel
def cuts58121 : List PrefixCut := [⟨2,6462648,6462651⟩,
⟨64,212563947,212564064⟩]
theorem checked58121 : checkPrefixCuts (2^48) 7621967873 10 Manual.Count131072.C058121.packed 64 cuts58121 = true := by
 decide +kernel
def pointBounds58121 : List (Nat × Nat × Nat) := [(7621971968,113523685653283,113524073836274)]
theorem point_links_checked58121 : (cuts58121.take 1).map (fun c => (7621967873-1+2*2^10*c.k,113523679190635+c.lower,113524067373623+c.upper)) = pointBounds58121 := by
 decide +kernel
def cuts58122 : List PrefixCut := [⟨55,182020664,182020766⟩,
⟨64,212117147,212117266⟩]
theorem checked58122 : checkPrefixCuts (2^48) 7622098945 10 Manual.Count131072.C058122.packed 64 cuts58122 = true := by
 decide +kernel
def pointBounds58122 : List (Nat × Nat × Nat) := [(7622211584,113524073775246,113524461958453)]
theorem point_links_checked58122 : (cuts58122.take 1).map (fun c => (7622098945-1+2*2^10*c.k,113523891754582+c.lower,113524279937687+c.upper)) = pointBounds58122 := by
 decide +kernel
def cuts58123 : List PrefixCut := [⟨64,212741266,212741387⟩]
theorem checked58123 : checkPrefixCuts (2^48) 7622230017 10 Manual.Count131072.C058123.packed 64 cuts58123 = true := by
 decide +kernel
def cuts58124 : List PrefixCut := [⟨44,143794907,143794991⟩,
⟨64,210152699,210152821⟩]
theorem checked58124 : checkPrefixCuts (2^48) 7622361089 10 Manual.Count131072.C058124.packed 64 cuts58124 = true := by
 decide +kernel
def pointBounds58124 : List (Nat × Nat × Nat) := [(7622451200,113524460407902,113524848591331)]
theorem point_links_checked58124 : (cuts58124.take 1).map (fun c => (7622361089-1+2*2^10*c.k,113524316612995+c.lower,113524704796340+c.upper)) = pointBounds58124 := by
 decide +kernel
def cuts58125 : List PrefixCut := [⟨64,215208030,215208153⟩]
theorem checked58125 : checkPrefixCuts (2^48) 7622492161 10 Manual.Count131072.C058125.packed 64 cuts58125 = true := by
 decide +kernel
def cuts58126 : List PrefixCut := [⟨33,111922968,111923031⟩,
⟨64,212619543,212619662⟩]
theorem checked58126 : checkPrefixCuts (2^48) 7622623233 10 Manual.Count131072.C058126.packed 64 cuts58126 = true := by
 decide +kernel
def pointBounds58126 : List (Nat × Nat × Nat) := [(7622690816,113524853896692,113525242080345)]
theorem point_links_checked58126 : (cuts58126.take 1).map (fun c => (7622623233-1+2*2^10*c.k,113524741973724+c.lower,113525130157314+c.upper)) = pointBounds58126 := by
 decide +kernel
def cuts58127 : List PrefixCut := [⟨64,212505091,212505208⟩]
theorem checked58127 : checkPrefixCuts (2^48) 7622754305 10 Manual.Count131072.C058127.packed 64 cuts58127 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000253
