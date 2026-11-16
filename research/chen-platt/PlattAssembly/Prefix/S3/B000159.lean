import PlattAssemblyKernel
import PlattCertificates.Count131072.C025088
import PlattCertificates.Count131072.C025089
import PlattCertificates.Count131072.C025090
import PlattCertificates.Count131072.C025091
import PlattCertificates.Count131072.C025092
import PlattCertificates.Count131072.C025093
import PlattCertificates.Count131072.C025094
import PlattCertificates.Count131072.C025095
import PlattCertificates.Count131072.C025096
import PlattCertificates.Count131072.C025097
import PlattCertificates.Count131072.C025098
import PlattCertificates.Count131072.C025099
import PlattCertificates.Count131072.C025100
import PlattCertificates.Count131072.C025101
import PlattCertificates.Count131072.C025102
import PlattCertificates.Count131072.C025103
import PlattCertificates.Count131072.C025104
import PlattCertificates.Count131072.C025105
import PlattCertificates.Count131072.C025106
import PlattCertificates.Count131072.C025107
import PlattCertificates.Count131072.C025108
import PlattCertificates.Count131072.C025109
import PlattCertificates.Count131072.C025110
import PlattCertificates.Count131072.C025111
import PlattCertificates.Count131072.C025112
import PlattCertificates.Count131072.C025113
import PlattCertificates.Count131072.C025114
import PlattCertificates.Count131072.C025115
import PlattCertificates.Count131072.C025116
import PlattCertificates.Count131072.C025117
import PlattCertificates.Count131072.C025118
import PlattCertificates.Count131072.C025119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25088 : List PrefixCut := [⟨8,33770792,33770810⟩,
⟨109,435508168,435508407⟩,
⟨128,507407466,507407747⟩]
theorem checked25088 : checkPrefixCuts (2^48) 3292266497 9 Manual.Count131072.C025088.packed 128 cuts25088 = true := by
 decide +kernel
def pointBounds25088 : List (Nat × Nat × Nat) := [(3292274688,102943115209015,102943497250830),(3292378112,102943516946391,102943898988427)]
theorem point_links_checked25088 : (cuts25088.take 2).map (fun c => (3292266497-1+2*2^9*c.k,102943081438223+c.lower,102943463480020+c.upper)) = pointBounds25088 := by
 decide +kernel
def cuts25089 : List PrefixCut := [⟨82,327175119,327175296⟩,
⟨128,516620052,516620335⟩]
theorem checked25089 : checkPrefixCuts (2^48) 3292397569 9 Manual.Count131072.C025089.packed 128 cuts25089 = true := by
 decide +kernel
def pointBounds25089 : List (Nat × Nat × Nat) := [(3292481536,102943916020808,102944298063063)]
theorem point_links_checked25089 : (cuts25089.take 1).map (fun c => (3292397569-1+2*2^9*c.k,102943588845689+c.lower,102943970887767+c.upper)) = pointBounds25089 := by
 decide +kernel
def cuts25090 : List PrefixCut := [⟨55,219020885,219021010⟩,
⟨128,513265597,513265880⟩]
theorem checked25090 : checkPrefixCuts (2^48) 3292528641 9 Manual.Count131072.C025090.packed 128 cuts25090 = true := by
 decide +kernel
def pointBounds25090 : List (Nat × Nat × Nat) := [(3292584960,102944324486626,102944706529112)]
theorem point_links_checked25090 : (cuts25090.take 1).map (fun c => (3292528641-1+2*2^9*c.k,102944105465741+c.lower,102944487508102+c.upper)) = pointBounds25090 := by
 decide +kernel
def cuts25091 : List PrefixCut := [⟨28,113267894,113267958⟩,
⟨128,512817726,512818018⟩]
theorem checked25091 : checkPrefixCuts (2^48) 3292659713 9 Manual.Count131072.C025091.packed 128 cuts25091 = true := by
 decide +kernel
def pointBounds25091 : List (Nat × Nat × Nat) := [(3292688384,102944731999232,102945114041940)]
theorem point_links_checked25091 : (cuts25091.take 1).map (fun c => (3292659713-1+2*2^9*c.k,102944618731338+c.lower,102945000773982+c.upper)) = pointBounds25091 := by
 decide +kernel
def cuts25092 : List PrefixCut := [⟨1,4445072,4445075⟩,
⟨102,405349984,405350209⟩,
⟨128,510745719,510746005⟩]
theorem checked25092 : checkPrefixCuts (2^48) 3292790785 9 Manual.Count131072.C025092.packed 128 cuts25092 = true := by
 decide +kernel
def pointBounds25092 : List (Nat × Nat × Nat) := [(3292791808,102945135994136,102945518037075),(3292895232,102945536899048,102945918942209)]
theorem point_links_checked25092 : (cuts25092.take 2).map (fun c => (3292790785-1+2*2^9*c.k,102945131549064+c.lower,102945513592000+c.upper)) = pointBounds25092 := by
 decide +kernel
def cuts25093 : List PrefixCut := [⟨75,297804536,297804704⟩,
⟨128,516281408,516281695⟩]
theorem checked25093 : checkPrefixCuts (2^48) 3292921857 9 Manual.Count131072.C025093.packed 128 cuts25093 = true := by
 decide +kernel
def pointBounds25093 : List (Nat × Nat × Nat) := [(3292998656,102945940099319,102946322142709)]
theorem point_links_checked25093 : (cuts25093.take 1).map (fun c => (3292921857-1+2*2^9*c.k,102945642294783+c.lower,102946024338005+c.upper)) = pointBounds25093 := by
 decide +kernel
def cuts25094 : List PrefixCut := [⟨48,193514791,193514898⟩,
⟨128,514551495,514551778⟩]
theorem checked25094 : checkPrefixCuts (2^48) 3293052929 9 Manual.Count131072.C025094.packed 128 cuts25094 = true := by
 decide +kernel
def pointBounds25094 : List (Nat × Nat × Nat) := [(3293102080,102946352090982,102946734134598)]
theorem point_links_checked25094 : (cuts25094.take 1).map (fun c => (3293052929-1+2*2^9*c.k,102946158576191+c.lower,102946540619700+c.upper)) = pointBounds25094 := by
 decide +kernel
def cuts25095 : List PrefixCut := [⟨21,85813567,85813616⟩,
⟨122,490941620,490941892⟩,
⟨128,515812994,515813282⟩]
theorem checked25095 : checkPrefixCuts (2^48) 3293184001 9 Manual.Count131072.C025095.packed 128 cuts25095 = true := by
 decide +kernel
def pointBounds25095 : List (Nat × Nat × Nat) := [(3293205504,102946758941253,102947140985094),(3293308928,102947164069306,102947546113370)]
theorem point_links_checked25095 : (cuts25095.take 2).map (fun c => (3293184001-1+2*2^9*c.k,102946673127686+c.lower,102947055171478+c.upper)) = pointBounds25095 := by
 decide +kernel
def cuts25096 : List PrefixCut := [⟨95,373834012,373834225⟩,
⟨128,506476643,506476928⟩]
theorem checked25096 : checkPrefixCuts (2^48) 3293315073 9 Manual.Count131072.C025096.packed 128 cuts25096 = true := by
 decide +kernel
def pointBounds25096 : List (Nat × Nat × Nat) := [(3293412352,102947562774692,102947944818985)]
theorem point_links_checked25096 : (cuts25096.take 1).map (fun c => (3293315073-1+2*2^9*c.k,102947188940680+c.lower,102947570984760+c.upper)) = pointBounds25096 := by
 decide +kernel
def cuts25097 : List PrefixCut := [⟨68,267588604,267588757⟩,
⟨128,505174490,505174776⟩]
theorem checked25097 : checkPrefixCuts (2^48) 3293446145 9 Manual.Count131072.C025097.packed 128 cuts25097 = true := by
 decide +kernel
def pointBounds25097 : List (Nat × Nat × Nat) := [(3293515776,102947963005927,102948345050445)]
theorem point_links_checked25097 : (cuts25097.take 1).map (fun c => (3293446145-1+2*2^9*c.k,102947695417323+c.lower,102948077461688+c.upper)) = pointBounds25097 := by
 decide +kernel
def cuts25098 : List PrefixCut := [⟨41,167076657,167076749⟩,
⟨128,513102241,513102529⟩]
theorem checked25098 : checkPrefixCuts (2^48) 3293577217 9 Manual.Count131072.C025098.packed 128 cuts25098 = true := by
 decide +kernel
def pointBounds25098 : List (Nat × Nat × Nat) := [(3293619200,102948367668470,102948749713213)]
theorem point_links_checked25098 : (cuts25098.take 1).map (fun c => (3293577217-1+2*2^9*c.k,102948200591813+c.lower,102948582636464+c.upper)) = pointBounds25098 := by
 decide +kernel
def cuts25099 : List PrefixCut := [⟨14,53753190,53753223⟩,
⟨115,460014019,460014280⟩,
⟨128,513081651,513081945⟩]
theorem checked25099 : checkPrefixCuts (2^48) 3293708289 9 Manual.Count131072.C025099.packed 128 cuts25099 = true := by
 decide +kernel
def pointBounds25099 : List (Nat × Nat × Nat) := [(3293722624,102948767447244,102949149492216),(3293826048,102949173708073,102949555753273)]
theorem point_links_checked25099 : (cuts25099.take 2).map (fun c => (3293708289-1+2*2^9*c.k,102948713694054+c.lower,102949095738993+c.upper)) = pointBounds25099 := by
 decide +kernel
def cuts25100 : List PrefixCut := [⟨88,349762362,349762559⟩,
⟨128,509472302,509472591⟩]
theorem checked25100 : checkPrefixCuts (2^48) 3293839361 9 Manual.Count131072.C025100.packed 128 cuts25100 = true := by
 decide +kernel
def pointBounds25100 : List (Nat × Nat × Nat) := [(3293929472,102949576538067,102949958583497)]
theorem point_links_checked25100 : (cuts25100.take 1).map (fun c => (3293839361-1+2*2^9*c.k,102949226775705+c.lower,102949608820938+c.upper)) = pointBounds25100 := by
 decide +kernel
def cuts25101 : List PrefixCut := [⟨61,242936456,242936587⟩,
⟨128,512784557,512784844⟩]
theorem checked25101 : checkPrefixCuts (2^48) 3293970433 9 Manual.Count131072.C025101.packed 128 cuts25101 = true := by
 decide +kernel
def pointBounds25101 : List (Nat × Nat × Nat) := [(3294032896,102949979184463,102950361230116)]
theorem point_links_checked25101 : (cuts25101.take 1).map (fun c => (3293970433-1+2*2^9*c.k,102949736248007+c.lower,102950118293529+c.upper)) = pointBounds25101 := by
 decide +kernel
def cuts25102 : List PrefixCut := [⟨34,136118190,136118267⟩,
⟨128,509346355,509346642⟩]
theorem checked25102 : checkPrefixCuts (2^48) 3294101505 9 Manual.Count131072.C025102.packed 128 cuts25102 = true := by
 decide +kernel
def pointBounds25102 : List (Nat × Nat × Nat) := [(3294136320,102950385150754,102950767196640)]
theorem point_links_checked25102 : (cuts25102.take 1).map (fun c => (3294101505-1+2*2^9*c.k,102950249032564+c.lower,102950631078373+c.upper)) = pointBounds25102 := by
 decide +kernel
def cuts25103 : List PrefixCut := [⟨7,28709406,28709421⟩,
⟨108,431061625,431061875⟩,
⟨128,511291312,511291609⟩]
theorem checked25103 : checkPrefixCuts (2^48) 3294232577 9 Manual.Count131072.C025103.packed 128 cuts25103 = true := by
 decide +kernel
def pointBounds25103 : List (Nat × Nat × Nat) := [(3294239744,102950787088325,102951169134436),(3294343168,102951189440544,102951571486890)]
theorem point_links_checked25103 : (cuts25103.take 2).map (fun c => (3294232577-1+2*2^9*c.k,102950758378919+c.lower,102951140425015+c.upper)) = pointBounds25103 := by
 decide +kernel
def cuts25104 : List PrefixCut := [⟨81,323733228,323733407⟩,
⟨128,508280582,508280866⟩]
theorem checked25104 : checkPrefixCuts (2^48) 3294363649 9 Manual.Count131072.C025104.packed 128 cuts25104 = true := by
 decide +kernel
def pointBounds25104 : List (Nat × Nat × Nat) := [(3294446592,102951593403459,102951975450031)]
theorem point_links_checked25104 : (cuts25104.take 1).map (fun c => (3294363649-1+2*2^9*c.k,102951269670231+c.lower,102951651716624+c.upper)) = pointBounds25104 := by
 decide +kernel
def cuts25105 : List PrefixCut := [⟨54,214105751,214105879⟩,
⟨128,508687502,508687795⟩]
theorem checked25105 : checkPrefixCuts (2^48) 3294494721 9 Manual.Count131072.C025105.packed 128 cuts25105 = true := by
 decide +kernel
def pointBounds25105 : List (Nat × Nat × Nat) := [(3294550016,102951992056564,102952374103369)]
theorem point_links_checked25105 : (cuts25105.take 1).map (fun c => (3294494721-1+2*2^9*c.k,102951777950813+c.lower,102952159997490+c.upper)) = pointBounds25105 := by
 decide +kernel
def cuts25106 : List PrefixCut := [⟨27,108245127,108245191⟩,
⟨128,506104238,506104530⟩]
theorem checked25106 : checkPrefixCuts (2^48) 3294625793 9 Manual.Count131072.C025106.packed 128 cuts25106 = true := by
 decide +kernel
def pointBounds25106 : List (Nat × Nat × Nat) := [(3294653440,102952394883442,102952776930476),(3294756864,102952792742553,102953174789815)]
theorem point_links_checked25106 : (cuts25106.take 2).map (fun c => (3294625793-1+2*2^9*c.k,102952286638315+c.lower,102952668685285+c.upper)) = pointBounds25106 := by
 decide +kernel
def cuts25107 : List PrefixCut := [⟨101,403399565,403399785⟩,
⟨128,509415872,509416153⟩]
theorem checked25107 : checkPrefixCuts (2^48) 3294756865 9 Manual.Count131072.C025107.packed 128 cuts25107 = true := by
 decide +kernel
def pointBounds25107 : List (Nat × Nat × Nat) := [(3294860288,102953196142118,102953578189600)]
theorem point_links_checked25107 : (cuts25107.take 1).map (fun c => (3294756865-1+2*2^9*c.k,102952792742553+c.lower,102953174789815+c.upper)) = pointBounds25107 := by
 decide +kernel
def cuts25108 : List PrefixCut := [⟨74,296345492,296345660⟩,
⟨128,510677002,510677289⟩]
theorem checked25108 : checkPrefixCuts (2^48) 3294887937 9 Manual.Count131072.C025108.packed 128 cuts25108 = true := by
 decide +kernel
def pointBounds25108 : List (Nat × Nat × Nat) := [(3294963712,102953598503917,102953980551628)]
theorem point_links_checked25108 : (cuts25108.take 1).map (fun c => (3294887937-1+2*2^9*c.k,102953302158425+c.lower,102953684205968+c.upper)) = pointBounds25108 := by
 decide +kernel
def cuts25109 : List PrefixCut := [⟨47,188786468,188786572⟩,
⟨128,511938019,511938310⟩]
theorem checked25109 : checkPrefixCuts (2^48) 3295019009 9 Manual.Count131072.C025109.packed 128 cuts25109 = true := by
 decide +kernel
def pointBounds25109 : List (Nat × Nat × Nat) := [(3295067136,102954001621895,102954383669829)]
theorem point_links_checked25109 : (cuts25109.take 1).map (fun c => (3295019009-1+2*2^9*c.k,102953812835427+c.lower,102954194883257+c.upper)) = pointBounds25109 := by
 decide +kernel
def cuts25110 : List PrefixCut := [⟨20,78416204,78416246⟩,
⟨121,477067094,477067363⟩,
⟨128,503888238,503888522⟩]
theorem checked25110 : checkPrefixCuts (2^48) 3295150081 9 Manual.Count131072.C025110.packed 128 cuts25110 = true := by
 decide +kernel
def pointBounds25110 : List (Nat × Nat × Nat) := [(3295170560,102954403189650,102954785237813),(3295273984,102954801840540,102955183888930)]
theorem point_links_checked25110 : (cuts25110.take 2).map (fun c => (3295150081-1+2*2^9*c.k,102954324773446+c.lower,102954706821567+c.upper)) = pointBounds25110 := by
 decide +kernel
def cuts25111 : List PrefixCut := [⟨94,379163076,379163288⟩,
⟨128,512239061,512239353⟩]
theorem checked25111 : checkPrefixCuts (2^48) 3295281153 9 Manual.Count131072.C025111.packed 128 cuts25111 = true := by
 decide +kernel
def pointBounds25111 : List (Nat × Nat × Nat) := [(3295377408,102955207824760,102955589873377)]
theorem point_links_checked25111 : (cuts25111.take 1).map (fun c => (3295281153-1+2*2^9*c.k,102954828661684+c.lower,102955210710089+c.upper)) = pointBounds25111 := by
 decide +kernel
def cuts25112 : List PrefixCut := [⟨67,260766724,260766874⟩,
⟨128,503079367,503079654⟩]
theorem checked25112 : checkPrefixCuts (2^48) 3295412225 9 Manual.Count131072.C025112.packed 128 cuts25112 = true := by
 decide +kernel
def pointBounds25112 : List (Nat × Nat × Nat) := [(3295480832,102955601667469,102955983716316)]
theorem point_links_checked25112 : (cuts25112.take 1).map (fun c => (3295412225-1+2*2^9*c.k,102955340900745+c.lower,102955722949442+c.upper)) = pointBounds25112 := by
 decide +kernel
def cuts25113 : List PrefixCut := [⟨40,158521428,158521515⟩,
⟨128,513650152,513650438⟩]
theorem checked25113 : checkPrefixCuts (2^48) 3295543297 9 Manual.Count131072.C025113.packed 128 cuts25113 = true := by
 decide +kernel
def pointBounds25113 : List (Nat × Nat × Nat) := [(3295584256,102956002501540,102956384550611)]
theorem point_links_checked25113 : (cuts25113.take 1).map (fun c => (3295543297-1+2*2^9*c.k,102955843980112+c.lower,102956226029096+c.upper)) = pointBounds25113 := by
 decide +kernel
def cuts25114 : List PrefixCut := [⟨13,52098395,52098424⟩,
⟨114,461277065,461277315⟩,
⟨128,517814618,517814898⟩]
theorem checked25114 : checkPrefixCuts (2^48) 3295674369 9 Manual.Count131072.C025114.packed 128 cuts25114 = true := by
 decide +kernel
def pointBounds25114 : List (Nat × Nat × Nat) := [(3295687680,102956409728659,102956791777958),(3295791104,102956818907329,102957200956849)]
theorem point_links_checked25114 : (cuts25114.take 2).map (fun c => (3295674369-1+2*2^9*c.k,102956357630264+c.lower,102956739679534+c.upper)) = pointBounds25114 := by
 decide +kernel
def cuts25115 : List PrefixCut := [⟨87,345966840,345967035⟩,
⟨128,510791020,510791304⟩]
theorem checked25115 : checkPrefixCuts (2^48) 3295805441 9 Manual.Count131072.C025115.packed 128 cuts25115 = true := by
 decide +kernel
def pointBounds25115 : List (Nat × Nat × Nat) := [(3295894528,102957221411722,102957603461467)]
theorem point_links_checked25115 : (cuts25115.take 1).map (fun c => (3295805441-1+2*2^9*c.k,102956875444882+c.lower,102957257494432+c.upper)) = pointBounds25115 := by
 decide +kernel
def cuts25116 : List PrefixCut := [⟨60,239631805,239631938⟩,
⟨128,515723811,515724095⟩]
theorem checked25116 : checkPrefixCuts (2^48) 3295936513 9 Manual.Count131072.C025116.packed 128 cuts25116 = true := by
 decide +kernel
def pointBounds25116 : List (Nat × Nat × Nat) := [(3295997952,102957625867707,102958007917674)]
theorem point_links_checked25116 : (cuts25116.take 1).map (fun c => (3295936513-1+2*2^9*c.k,102957386235902+c.lower,102957768285736+c.upper)) = pointBounds25116 := by
 decide +kernel
def cuts25117 : List PrefixCut := [⟨33,130315437,130315512⟩,
⟨128,504943476,504943767⟩]
theorem checked25117 : checkPrefixCuts (2^48) 3296067585 9 Manual.Count131072.C025117.packed 128 cuts25117 = true := by
 decide +kernel
def pointBounds25117 : List (Nat × Nat × Nat) := [(3296101376,102958032275150,102958414325343)]
theorem point_links_checked25117 : (cuts25117.take 1).map (fun c => (3296067585-1+2*2^9*c.k,102957901959713+c.lower,102958284009831+c.upper)) = pointBounds25117 := by
 decide +kernel
def cuts25118 : List PrefixCut := [⟨6,24081026,24081041⟩,
⟨107,426022564,426022807⟩,
⟨128,508509962,508510250⟩]
theorem checked25118 : checkPrefixCuts (2^48) 3296198657 9 Manual.Count131072.C025118.packed 128 cuts25118 = true := by
 decide +kernel
def pointBounds25118 : List (Nat × Nat × Nat) := [(3296204800,102958430984215,102958813034639),(3296308224,102958832925753,102959214976405)]
theorem point_links_checked25118 : (cuts25118.take 2).map (fun c => (3296198657-1+2*2^9*c.k,102958406903189+c.lower,102958788953598+c.upper)) = pointBounds25118 := by
 decide +kernel
def cuts25119 : List PrefixCut := [⟨80,322857041,322857226⟩,
⟨128,516516226,516516520⟩]
theorem checked25119 : checkPrefixCuts (2^48) 3296329729 9 Manual.Count131072.C025119.packed 128 cuts25119 = true := by
 decide +kernel
def pointBounds25119 : List (Nat × Nat × Nat) := [(3296411648,102959238270192,102959620321074)]
theorem point_links_checked25119 : (cuts25119.take 1).map (fun c => (3296329729-1+2*2^9*c.k,102958915413151+c.lower,102959297463848+c.upper)) = pointBounds25119 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000159
