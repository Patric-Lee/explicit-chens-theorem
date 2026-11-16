import PlattAssemblyKernel
import PlattCertificates.Count131072.C013136
import PlattCertificates.Count131072.C013137
import PlattCertificates.Count131072.C013138
import PlattCertificates.Count131072.C013139
import PlattCertificates.Count131072.C013140
import PlattCertificates.Count131072.C013141
import PlattCertificates.Count131072.C013142
import PlattCertificates.Count131072.C013143
import PlattCertificates.Count131072.C013144
import PlattCertificates.Count131072.C013145
import PlattCertificates.Count131072.C013146
import PlattCertificates.Count131072.C013147
import PlattCertificates.Count131072.C013148
import PlattCertificates.Count131072.C013149
import PlattCertificates.Count131072.C013150
import PlattCertificates.Count131072.C013151
import PlattCertificates.Count131072.C013152
import PlattCertificates.Count131072.C013153
import PlattCertificates.Count131072.C013154
import PlattCertificates.Count131072.C013155
import PlattCertificates.Count131072.C013156
import PlattCertificates.Count131072.C013157
import PlattCertificates.Count131072.C013158
import PlattCertificates.Count131072.C013159
import PlattCertificates.Count131072.C013160
import PlattCertificates.Count131072.C013161
import PlattCertificates.Count131072.C013162
import PlattCertificates.Count131072.C013163
import PlattCertificates.Count131072.C013164
import PlattCertificates.Count131072.C013165
import PlattCertificates.Count131072.C013166
import PlattCertificates.Count131072.C013167
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000098
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13136 : List PrefixCut := [⟨51,400098424,400098709⟩,
⟨104,818288642,818289225⟩,
⟨128,1006502580,1006503297⟩]
theorem checked13136 : checkPrefixCuts (2^48) 1725693953 9 Manual.Count131072.C013136.packed 128 cuts13136 = true := by
 decide +kernel
def pointBounds13136 : List (Nat × Nat × Nat) := [(1725746176,94522407548234,94522784372997),(1725800448,94522825738452,94523202563513)]
theorem point_links_checked13136 : (cuts13136.take 2).map (fun c => (1725693953-1+2*2^9*c.k,94522007449810+c.lower,94522384274288+c.upper)) = pointBounds13136 := by
 decide +kernel
def cuts13137 : List PrefixCut := [⟨29,222134583,222134748⟩,
⟨82,643234126,643234591⟩,
⟨128,1009361464,1009362193⟩]
theorem checked13137 : checkPrefixCuts (2^48) 1725825025 9 Manual.Count131072.C013137.packed 128 cuts13137 = true := by
 decide +kernel
def pointBounds13137 : List (Nat × Nat × Nat) := [(1725854720,94523236086973,94523612912333),(1725908992,94523657186516,94524034012176)]
theorem point_links_checked13137 : (cuts13137.take 2).map (fun c => (1725825025-1+2*2^9*c.k,94523013952390+c.lower,94523390777585+c.upper)) = pointBounds13137 := by
 decide +kernel
def cuts13138 : List PrefixCut := [⟨7,57405254,57405294⟩,
⟨60,465105794,465106131⟩,
⟨113,893667090,893667735⟩,
⟨128,1015807868,1015808602⟩]
theorem checked13138 : checkPrefixCuts (2^48) 1725956097 9 Manual.Count131072.C013138.packed 128 cuts13138 = true := by
 decide +kernel
def pointBounds13138 : List (Nat × Nat × Nat) := [(1725963264,94524080719108,94524457545072),(1726017536,94524488419648,94524865245909),(1726071808,94524916980944,94525293807513)]
theorem point_links_checked13138 : (cuts13138.take 3).map (fun c => (1725956097-1+2*2^9*c.k,94524023313854+c.lower,94524400139778+c.upper)) = pointBounds13138 := by
 decide +kernel
def cuts13139 : List PrefixCut := [⟨38,298905864,298906078⟩,
⟨91,714884182,714884697⟩,
⟨128,1001218405,1001219130⟩]
theorem checked13139 : checkPrefixCuts (2^48) 1726087169 9 Manual.Count131072.C013139.packed 128 cuts13139 = true := by
 decide +kernel
def pointBounds13139 : List (Nat × Nat × Nat) := [(1726126080,94525338027586,94525714854458),(1726180352,94525754005904,94526130833077)]
theorem point_links_checked13139 : (cuts13139.take 2).map (fun c => (1726087169-1+2*2^9*c.k,94525039121722+c.lower,94525415948380+c.upper)) = pointBounds13139 := by
 decide +kernel
def cuts13140 : List PrefixCut := [⟨16,122456509,122456596⟩,
⟨69,534658424,534658810⟩,
⟨122,953532447,953533130⟩,
⟨128,1000326824,1000327542⟩]
theorem checked13140 : checkPrefixCuts (2^48) 1726218241 9 Manual.Count131072.C013140.packed 128 cuts13140 = true := by
 decide +kernel
def pointBounds13140 : List (Nat × Nat × Nat) := [(1726234624,94526162796636,94526539624106),(1726288896,94526574998551,94526951826320),(1726343168,94526993872574,94527370700640)]
theorem point_links_checked13140 : (cuts13140.take 3).map (fun c => (1726218241-1+2*2^9*c.k,94526040340127+c.lower,94526417167510+c.upper)) = pointBounds13140 := by
 decide +kernel
def cuts13141 : List PrefixCut := [⟨47,364240317,364240577⟩,
⟨100,787326990,787327548⟩,
⟨128,1007424603,1007425320⟩]
theorem checked13141 : checkPrefixCuts (2^48) 1726349313 9 Manual.Count131072.C013141.packed 128 cuts13141 = true := by
 decide +kernel
def pointBounds13141 : List (Nat × Nat × Nat) := [(1726397440,94527404907268,94527781735629),(1726451712,94527827993941,94528204822600)]
theorem point_links_checked13141 : (cuts13141.take 2).map (fun c => (1726349313-1+2*2^9*c.k,94527040666951+c.lower,94527417495052+c.upper)) = pointBounds13141 := by
 decide +kernel
def cuts13142 : List PrefixCut := [⟨25,198573884,198574027⟩,
⟨78,613156515,613156954⟩,
⟨128,1001479595,1001480317⟩]
theorem checked13142 : checkPrefixCuts (2^48) 1726480385 9 Manual.Count131072.C013142.packed 128 cuts13142 = true := by
 decide +kernel
def pointBounds13142 : List (Nat × Nat × Nat) := [(1726505984,94528246665438,94528623494399),(1726560256,94528661248069,94529038077326)]
theorem point_links_checked13142 : (cuts13142.take 2).map (fun c => (1726480385-1+2*2^9*c.k,94528048091554+c.lower,94528424920372+c.upper)) = pointBounds13142 := by
 decide +kernel
def cuts13143 : List PrefixCut := [⟨3,23475083,23475099⟩,
⟨56,451236076,451236398⟩,
⟨109,872626128,872626752⟩,
⟨128,1026670671,1026671408⟩]
theorem checked13143 : checkPrefixCuts (2^48) 1726611457 9 Manual.Count131072.C013143.packed 128 cuts13143 = true := by
 decide +kernel
def pointBounds13143 : List (Nat × Nat × Nat) := [(1726614528,94529073046232,94529449875788),(1726668800,94529500807225,94529877637087),(1726723072,94529922197277,94530299027441)]
theorem point_links_checked13143 : (cuts13143.take 3).map (fun c => (1726611457-1+2*2^9*c.k,94529049571149+c.lower,94529426400689+c.upper)) = pointBounds13143 := by
 decide +kernel
def cuts13144 : List PrefixCut := [⟨34,269288457,269288653⟩,
⟨87,682827783,682828278⟩,
⟨128,1007521383,1007522107⟩]
theorem checked13144 : checkPrefixCuts (2^48) 1726742529 9 Manual.Count131072.C013144.packed 128 cuts13144 = true := by
 decide +kernel
def pointBounds13144 : List (Nat × Nat × Nat) := [(1726777344,94530345530277,94530722360750),(1726831616,94530759069603,94531135900375)]
theorem point_links_checked13144 : (cuts13144.take 2).map (fun c => (1726742529-1+2*2^9*c.k,94530076241820+c.lower,94530453072097+c.upper)) = pointBounds13144 := by
 decide +kernel
def cuts13145 : List PrefixCut := [⟨12,94700799,94700866⟩,
⟨65,515548920,515549289⟩,
⟨118,936057767,936058439⟩,
⟨128,1015920368,1015921098⟩]
theorem checked13145 : checkPrefixCuts (2^48) 1726873601 9 Manual.Count131072.C013145.packed 128 cuts13145 = true := by
 decide +kernel
def pointBounds13145 : List (Nat × Nat × Nat) := [(1726885888,94531178464002,94531555295070),(1726940160,94531599312123,94531976143493),(1726994432,94532019820970,94532396652643)]
theorem point_links_checked13145 : (cuts13145.take 3).map (fun c => (1726873601-1+2*2^9*c.k,94531083763203+c.lower,94531460594204+c.upper)) = pointBounds13145 := by
 decide +kernel
def cuts13146 : List PrefixCut := [⟨43,328409436,328409675⟩,
⟨96,739439295,739439829⟩,
⟨128,991233518,991234236⟩]
theorem checked13146 : checkPrefixCuts (2^48) 1727004673 9 Manual.Count131072.C013146.packed 128 cuts13146 = true := by
 decide +kernel
def pointBounds13146 : List (Nat × Nat × Nat) := [(1727048704,94532428093007,94532804924977),(1727102976,94532839122866,94533215955131)]
theorem point_links_checked13146 : (cuts13146.take 2).map (fun c => (1727004673-1+2*2^9*c.k,94532099683571+c.lower,94532476515302+c.upper)) = pointBounds13146 := by
 decide +kernel
def cuts13147 : List PrefixCut := [⟨21,165252615,165252736⟩,
⟨74,581471453,581471874⟩,
⟨127,1000121704,1000122426⟩,
⟨128,1007943772,1007944499⟩]
theorem checked13147 : checkPrefixCuts (2^48) 1727135745 9 Manual.Count131072.C013147.packed 128 cuts13147 = true := by
 decide +kernel
def pointBounds13147 : List (Nat × Nat × Nat) := [(1727157248,94533256169704,94533633002274),(1727211520,94533672388542,94534049221412),(1727265792,94534091038793,94534467871964)]
theorem point_links_checked13147 : (cuts13147.take 3).map (fun c => (1727135745-1+2*2^9*c.k,94533090917089+c.lower,94533467749538+c.upper)) = pointBounds13147 := by
 decide +kernel
def cuts13148 : List PrefixCut := [⟨52,410000330,410000624⟩,
⟨105,816077070,816077656⟩,
⟨128,994179732,994180450⟩]
theorem checked13148 : checkPrefixCuts (2^48) 1727266817 9 Manual.Count131072.C013148.packed 128 cuts13148 = true := by
 decide +kernel
def pointBounds13148 : List (Nat × Nat × Nat) := [(1727320064,94534508861191,94534885694661),(1727374336,94534914937931,94535291771693)]
theorem point_links_checked13148 : (cuts13148.take 2).map (fun c => (1727266817-1+2*2^9*c.k,94534098860861+c.lower,94534475694037+c.upper)) = pointBounds13148 := by
 decide +kernel
def cuts13149 : List PrefixCut := [⟨30,232686720,232686889⟩,
⟨83,648351363,648351827⟩,
⟨128,1001436163,1001436878⟩]
theorem checked13149 : checkPrefixCuts (2^48) 1727397889 9 Manual.Count131072.C013149.packed 128 cuts13149 = true := by
 decide +kernel
def pointBounds13149 : List (Nat × Nat × Nat) := [(1727428608,94535325727313,94535702561376),(1727482880,94535741391956,94536118226314)]
theorem point_links_checked13149 : (cuts13149.take 2).map (fun c => (1727397889-1+2*2^9*c.k,94535093040593+c.lower,94535469874487+c.upper)) = pointBounds13149 := by
 decide +kernel
def cuts13150 : List PrefixCut := [⟨8,66151439,66151487⟩,
⟨61,483745295,483745643⟩,
⟨114,893179631,893180275⟩,
⟨128,1000871929,1000872651⟩]
theorem checked13150 : checkPrefixCuts (2^48) 1727528961 9 Manual.Count131072.C013150.packed 128 cuts13150 = true := by
 decide +kernel
def pointBounds13150 : List (Nat × Nat × Nat) := [(1727537152,94536160628195,94536537462852),(1727591424,94536578222051,94536955057008),(1727645696,94536987656387,94537364491640)]
theorem point_links_checked13150 : (cuts13150.take 3).map (fun c => (1727528961-1+2*2^9*c.k,94536094476756+c.lower,94536471311365+c.upper)) = pointBounds13150 := by
 decide +kernel
def cuts13151 : List PrefixCut := [⟨39,303684252,303684471⟩,
⟨92,711626581,711627095⟩,
⟨128,998351672,998352390⟩]
theorem checked13151 : checkPrefixCuts (2^48) 1727660033 9 Manual.Count131072.C013151.packed 128 cuts13151 = true := by
 decide +kernel
def pointBounds13151 : List (Nat × Nat × Nat) := [(1727699968,94537399032937,94537775868487),(1727754240,94537806975266,94538183811111)]
theorem point_links_checked13151 : (cuts13151.take 2).map (fun c => (1727660033-1+2*2^9*c.k,94537095348685+c.lower,94537472184016+c.upper)) = pointBounds13151 := by
 decide +kernel
def cuts13152 : List PrefixCut := [⟨17,132445363,132445460⟩,
⟨70,539058901,539059295⟩,
⟨123,966185162,966185863⟩,
⟨128,1002348547,1002349276⟩]
theorem checked13152 : checkPrefixCuts (2^48) 1727791105 9 Manual.Count131072.C013152.packed 128 cuts13152 = true := by
 decide +kernel
def pointBounds13152 : List (Nat × Nat × Nat) := [(1727808512,94538226145720,94538602981866),(1727862784,94538632759258,94539009595701),(1727917056,94539059885519,94539436722269)]
theorem point_links_checked13152 : (cuts13152.take 3).map (fun c => (1727791105-1+2*2^9*c.k,94538093700357+c.lower,94538470536406+c.upper)) = pointBounds13152 := by
 decide +kernel
def cuts13153 : List PrefixCut := [⟨48,367818223,367818487⟩,
⟨101,785144133,785144698⟩,
⟨128,999828996,999829715⟩]
theorem checked13153 : checkPrefixCuts (2^48) 1727922177 9 Manual.Count131072.C013153.packed 128 cuts13153 = true := by
 decide +kernel
def pointBounds13153 : List (Nat × Nat × Nat) := [(1727971328,94539463867127,94539840704169),(1728025600,94539881193037,94540258030380)]
theorem point_links_checked13153 : (cuts13153.take 2).map (fun c => (1727922177-1+2*2^9*c.k,94539096048904+c.lower,94539472885682+c.upper)) = pointBounds13153 := by
 decide +kernel
def cuts13154 : List PrefixCut := [⟨26,197252866,197253009⟩,
⟨79,608363132,608363574⟩,
⟨128,990469183,990469902⟩]
theorem checked13154 : checkPrefixCuts (2^48) 1728053249 9 Manual.Count131072.C013154.packed 128 cuts13154 = true := by
 decide +kernel
def pointBounds13154 : List (Nat × Nat × Nat) := [(1728079872,94540293130766,94540669968406),(1728134144,94540704241032,94541081078971)]
theorem point_links_checked13154 : (cuts13154.take 2).map (fun c => (1728053249-1+2*2^9*c.k,94540095877900+c.lower,94540472715397+c.upper)) = pointBounds13154 := by
 decide +kernel
def cuts13155 : List PrefixCut := [⟨4,32411725,32411748⟩,
⟨57,451639686,451640008⟩,
⟨110,865154232,865154853⟩,
⟨128,1003749546,1003750264⟩]
theorem checked13155 : checkPrefixCuts (2^48) 1728184321 9 Manual.Count131072.C013155.packed 128 cuts13155 = true := by
 decide +kernel
def pointBounds13155 : List (Nat × Nat × Nat) := [(1728188416,94541118758808,94541495597047),(1728242688,94541537986769,94541914825307),(1728296960,94541951501315,94542328340152)]
theorem point_links_checked13155 : (cuts13155.take 3).map (fun c => (1728184321-1+2*2^9*c.k,94541086347083+c.lower,94541463185299+c.upper)) = pointBounds13155 := by
 decide +kernel
def cuts13156 : List PrefixCut := [⟨35,280606293,280606499⟩,
⟨88,704029073,704029581⟩,
⟨128,1020610314,1020611046⟩]
theorem checked13156 : checkPrefixCuts (2^48) 1728315393 9 Manual.Count131072.C013156.packed 128 cuts13156 = true := by
 decide +kernel
def pointBounds13156 : List (Nat × Nat × Nat) := [(1728351232,94542370702922,94542747542062),(1728405504,94542794125702,94543170965144)]
theorem point_links_checked13156 : (cuts13156.take 2).map (fun c => (1728315393-1+2*2^9*c.k,94542090096629+c.lower,94542466935563+c.upper)) = pointBounds13156 := by
 decide +kernel
def cuts13157 : List PrefixCut := [⟨13,101128527,101128601⟩,
⟨66,518499313,518499687⟩,
⟨119,922992746,922993413⟩,
⟨128,991546942,991547659⟩]
theorem checked13157 : checkPrefixCuts (2^48) 1728446465 9 Manual.Count131072.C013157.packed 128 cuts13157 = true := by
 decide +kernel
def pointBounds13157 : List (Nat × Nat × Nat) := [(1728459776,94543211835470,94543588675210),(1728514048,94543629206256,94544006046296),(1728568320,94544033699689,94544410540022)]
theorem point_links_checked13157 : (cuts13157.take 3).map (fun c => (1728446465-1+2*2^9*c.k,94543110706943+c.lower,94543487546609+c.upper)) = pointBounds13157 := by
 decide +kernel
def cuts13158 : List PrefixCut := [⟨44,340974507,340974752⟩,
⟨97,763516693,763517240⟩,
⟨128,1008405874,1008406600⟩]
theorem checked13158 : checkPrefixCuts (2^48) 1728577537 9 Manual.Count131072.C013158.packed 128 cuts13158 = true := by
 decide +kernel
def pointBounds13158 : List (Nat × Nat × Nat) := [(1728622592,94544443228392,94544820069020),(1728676864,94544865770578,94545242611508)]
theorem point_links_checked13158 : (cuts13158.take 2).map (fun c => (1728577537-1+2*2^9*c.k,94544102253885+c.lower,94544479094268+c.upper)) = pointBounds13158 := by
 decide +kernel
def cuts13159 : List PrefixCut := [⟨22,176011382,176011511⟩,
⟨75,579802733,579803158⟩,
⟨128,1000514148,1000514876⟩]
theorem checked13159 : checkPrefixCuts (2^48) 1728708609 9 Manual.Count131072.C013159.packed 128 cuts13159 = true := by
 decide +kernel
def pointBounds13159 : List (Nat × Nat × Nat) := [(1728731136,94545286671141,94545663512379),(1728785408,94545690462492,94546067304026),(1728839680,94546111173907,94546488015744)]
theorem point_links_checked13159 : (cuts13159.take 3).map (fun c => (1728708609-1+2*2^9*c.k,94545110659759+c.lower,94545487500868+c.upper)) = pointBounds13159 := by
 decide +kernel
def cuts13160 : List PrefixCut := [⟨53,419558433,419558742⟩,
⟨106,830963575,830964180⟩,
⟨128,1011671754,1011672484⟩]
theorem checked13160 : checkPrefixCuts (2^48) 1728839681 9 Manual.Count131072.C013160.packed 128 cuts13160 = true := by
 decide +kernel
def pointBounds13160 : List (Nat × Nat × Nat) := [(1728893952,94546530732340,94546907574486),(1728948224,94546942137482,94547318979924)]
theorem point_links_checked13160 : (cuts13160.take 2).map (fun c => (1728839681-1+2*2^9*c.k,94546111173907+c.lower,94546488015744+c.upper)) = pointBounds13160 := by
 decide +kernel
def cuts13161 : List PrefixCut := [⟨31,245335964,245336141⟩,
⟨84,660785155,660785632⟩,
⟨128,1008339360,1008340084⟩]
theorem checked13161 : checkPrefixCuts (2^48) 1728970753 9 Manual.Count131072.C013161.packed 128 cuts13161 = true := by
 decide +kernel
def pointBounds13161 : List (Nat × Nat × Nat) := [(1729002496,94547368181625,94547745024369),(1729056768,94547783630816,94548160473860)]
theorem point_links_checked13161 : (cuts13161.take 2).map (fun c => (1728970753-1+2*2^9*c.k,94547122845661+c.lower,94547499688228+c.upper)) = pointBounds13161 := by
 decide +kernel
def cuts13162 : List PrefixCut := [⟨9,72277132,72277184⟩,
⟨62,477933218,477933564⟩,
⟨115,904412159,904412811⟩,
⟨128,1005821015,1005821741⟩]
theorem checked13162 : checkPrefixCuts (2^48) 1729101825 9 Manual.Count131072.C013162.packed 128 cuts13162 = true := by
 decide +kernel
def pointBounds13162 : List (Nat × Nat × Nat) := [(1729111040,94548203462153,94548580305496),(1729165312,94548609118239,94548985961876),(1729219584,94549035597180,94549412441123)]
theorem point_links_checked13162 : (cuts13162.take 3).map (fun c => (1729101825-1+2*2^9*c.k,94548131185021+c.lower,94548508028312+c.upper)) = pointBounds13162 := by
 decide +kernel
def cuts13163 : List PrefixCut := [⟨40,313011492,313011720⟩,
⟨93,728069879,728070406⟩,
⟨128,1006884250,1006884977⟩]
theorem checked13163 : checkPrefixCuts (2^48) 1729232897 9 Manual.Count131072.C013163.packed 128 cuts13163 = true := by
 decide +kernel
def pointBounds13163 : List (Nat × Nat × Nat) := [(1729273856,94549450017528,94549826861773),(1729328128,94549865075915,94550241920459)]
theorem point_links_checked13163 : (cuts13163.take 2).map (fun c => (1729232897-1+2*2^9*c.k,94549137006036+c.lower,94549513850053+c.upper)) = pointBounds13163 := by
 decide +kernel
def cuts13164 : List PrefixCut := [⟨18,141113981,141114084⟩,
⟨71,558587722,558588120⟩,
⟨124,970514750,970515449⟩,
⟨128,1001925488,1001926209⟩]
theorem checked13164 : checkPrefixCuts (2^48) 1729363969 9 Manual.Count131072.C013164.packed 128 cuts13164 = true := by
 decide +kernel
def pointBounds13164 : List (Nat × Nat × Nat) := [(1729382400,94550285004267,94550661849114),(1729436672,94550702478008,94551079323150),(1729490944,94551114405036,94551491250479)]
theorem point_links_checked13164 : (cuts13164.take 3).map (fun c => (1729363969-1+2*2^9*c.k,94550143890286+c.lower,94550520735030+c.upper)) = pointBounds13164 := by
 decide +kernel
def cuts13165 : List PrefixCut := [⟨49,385548578,385548860⟩,
⟨102,802494787,802495369⟩,
⟨128,1003965248,1003965973⟩]
theorem checked13165 : checkPrefixCuts (2^48) 1729495041 9 Manual.Count131072.C013165.packed 128 cuts13165 = true := by
 decide +kernel
def pointBounds13165 : List (Nat × Nat × Nat) := [(1729545216,94551531364352,94551908210099),(1729599488,94551948310561,94552325156608)]
theorem point_links_checked13165 : (cuts13165.take 2).map (fun c => (1729495041-1+2*2^9*c.k,94551145815774+c.lower,94551522661239+c.upper)) = pointBounds13165 := by
 decide +kernel
def cuts13166 : List PrefixCut := [⟨27,206512102,206512250⟩,
⟨80,616434709,616435154⟩,
⟨128,990219506,990220219⟩]
theorem checked13166 : checkPrefixCuts (2^48) 1729626113 9 Manual.Count131072.C013166.packed 128 cuts13166 = true := by
 decide +kernel
def pointBounds13166 : List (Nat × Nat × Nat) := [(1729653760,94552356293124,94552733139462),(1729708032,94552766215731,94553143062366)]
theorem point_links_checked13166 : (cuts13166.take 2).map (fun c => (1729626113-1+2*2^9*c.k,94552149781022+c.lower,94552526627212+c.upper)) = pointBounds13166 := by
 decide +kernel
def cuts13167 : List PrefixCut := [⟨5,44423884,44423916⟩,
⟨58,466850332,466850667⟩,
⟨111,879500474,879501105⟩,
⟨128,1009183198,1009183923⟩]
theorem checked13167 : checkPrefixCuts (2^48) 1729757185 9 Manual.Count131072.C013167.packed 128 cuts13167 = true := by
 decide +kernel
def pointBounds13167 : List (Nat × Nat × Nat) := [(1729762304,94553184424412,94553561271347),(1729816576,94553606850860,94553983698098),(1729870848,94554019501002,94554396348536)]
theorem point_links_checked13167 : (cuts13167.take 3).map (fun c => (1729757185-1+2*2^9*c.k,94553140000528+c.lower,94553516847431+c.upper)) = pointBounds13167 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000098
