import PlattAssemblyKernel
import PlattCertificates.Count131072.C027072
import PlattCertificates.Count131072.C027073
import PlattCertificates.Count131072.C027074
import PlattCertificates.Count131072.C027075
import PlattCertificates.Count131072.C027076
import PlattCertificates.Count131072.C027077
import PlattCertificates.Count131072.C027078
import PlattCertificates.Count131072.C027079
import PlattCertificates.Count131072.C027080
import PlattCertificates.Count131072.C027081
import PlattCertificates.Count131072.C027082
import PlattCertificates.Count131072.C027083
import PlattCertificates.Count131072.C027084
import PlattCertificates.Count131072.C027085
import PlattCertificates.Count131072.C027086
import PlattCertificates.Count131072.C027087
import PlattCertificates.Count131072.C027088
import PlattCertificates.Count131072.C027089
import PlattCertificates.Count131072.C027090
import PlattCertificates.Count131072.C027091
import PlattCertificates.Count131072.C027092
import PlattCertificates.Count131072.C027093
import PlattCertificates.Count131072.C027094
import PlattCertificates.Count131072.C027095
import PlattCertificates.Count131072.C027096
import PlattCertificates.Count131072.C027097
import PlattCertificates.Count131072.C027098
import PlattCertificates.Count131072.C027099
import PlattCertificates.Count131072.C027100
import PlattCertificates.Count131072.C027101
import PlattCertificates.Count131072.C027102
import PlattCertificates.Count131072.C027103
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000221
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27072 : List PrefixCut := [⟨92,340714843,340715037⟩,
⟨128,476443649,476443917⟩]
theorem checked27072 : checkPrefixCuts (2^48) 3552313345 9 Manual.Count131072.C027072.packed 128 cuts27072 = true := by
 decide +kernel
def pointBounds27072 : List (Nat × Nat × Nat) := [(3552407552,103918254375461,103918636963152)]
theorem point_links_checked27072 : (cuts27072.take 1).map (fun c => (3552313345-1+2*2^9*c.k,103917913660618+c.lower,103918296248115+c.upper)) = pointBounds27072 := by
 decide +kernel
def cuts27073 : List PrefixCut := [⟨73,270502514,270502665⟩,
⟨128,472702179,472702444⟩]
theorem checked27073 : checkPrefixCuts (2^48) 3552444417 9 Manual.Count131072.C027073.packed 128 cuts27073 = true := by
 decide +kernel
def pointBounds27073 : List (Nat × Nat × Nat) := [(3552519168,103918660606781,103919043194697)]
theorem point_links_checked27073 : (cuts27073.take 1).map (fun c => (3552444417-1+2*2^9*c.k,103918390104267+c.lower,103918772692032+c.upper)) = pointBounds27073 := by
 decide +kernel
def cuts27074 : List PrefixCut := [⟨54,195858064,195858173⟩,
⟨128,474110843,474111109⟩]
theorem checked27074 : checkPrefixCuts (2^48) 3552575489 9 Manual.Count131072.C027074.packed 128 cuts27074 = true := by
 decide +kernel
def pointBounds27074 : List (Nat × Nat × Nat) := [(3552630784,103919058664510,103919441252649)]
theorem point_links_checked27074 : (cuts27074.take 1).map (fun c => (3552575489-1+2*2^9*c.k,103918862806446+c.lower,103919245394476+c.upper)) = pointBounds27074 := by
 decide +kernel
def cuts27075 : List PrefixCut := [⟨35,128428416,128428488⟩,
⟨128,475123323,475123588⟩]
theorem checked27075 : checkPrefixCuts (2^48) 3552706561 9 Manual.Count131072.C027075.packed 128 cuts27075 = true := by
 decide +kernel
def pointBounds27075 : List (Nat × Nat × Nat) := [(3552742400,103919465345705,103919847934073)]
theorem point_links_checked27075 : (cuts27075.take 1).map (fun c => (3552706561-1+2*2^9*c.k,103919336917289+c.lower,103919719505585+c.upper)) = pointBounds27075 := by
 decide +kernel
def cuts27076 : List PrefixCut := [⟨16,58151291,58151324⟩,
⟨125,460766432,460766691⟩,
⟨128,472095247,472095512⟩]
theorem checked27076 : checkPrefixCuts (2^48) 3552837633 9 Manual.Count131072.C027076.packed 128 cuts27076 = true := by
 decide +kernel
def pointBounds27076 : List (Nat × Nat × Nat) := [(3552854016,103919870191903,103920252780497),(3552965632,103920272807044,103920655395864)]
theorem point_links_checked27076 : (cuts27076.take 2).map (fun c => (3552837633-1+2*2^9*c.k,103919812040612+c.lower,103920194629173+c.upper)) = pointBounds27076 := by
 decide +kernel
def cuts27077 : List PrefixCut := [⟨106,387867210,387867426⟩,
⟨128,469225926,469226188⟩]
theorem checked27077 : checkPrefixCuts (2^48) 3552968705 9 Manual.Count131072.C027077.packed 128 cuts27077 = true := by
 decide +kernel
def pointBounds27077 : List (Nat × Nat × Nat) := [(3553077248,103920672003069,103921054592111)]
theorem point_links_checked27077 : (cuts27077.take 1).map (fun c => (3552968705-1+2*2^9*c.k,103920284135859+c.lower,103920666724685+c.upper)) = pointBounds27077 := by
 decide +kernel
def cuts27078 : List PrefixCut := [⟨87,318537713,318537891⟩,
⟨128,470159196,470159462⟩]
theorem checked27078 : checkPrefixCuts (2^48) 3553099777 9 Manual.Count131072.C027078.packed 128 cuts27078 = true := by
 decide +kernel
def pointBounds27078 : List (Nat × Nat × Nat) := [(3553188864,103921071899498,103921454488764)]
theorem point_links_checked27078 : (cuts27078.take 1).map (fun c => (3553099777-1+2*2^9*c.k,103920753361785+c.lower,103921135950873+c.upper)) = pointBounds27078 := by
 decide +kernel
def cuts27079 : List PrefixCut := [⟨68,249213014,249213155⟩,
⟨128,469112083,469112350⟩]
theorem checked27079 : checkPrefixCuts (2^48) 3553230849 9 Manual.Count131072.C027079.packed 128 cuts27079 = true := by
 decide +kernel
def pointBounds27079 : List (Nat × Nat × Nat) := [(3553300480,103921472733995,103921855323490)]
theorem point_links_checked27079 : (cuts27079.take 1).map (fun c => (3553230849-1+2*2^9*c.k,103921223520981+c.lower,103921606110335+c.upper)) = pointBounds27079 := by
 decide +kernel
def cuts27080 : List PrefixCut := [⟨49,181318864,181318964⟩,
⟨128,472580140,472580406⟩]
theorem checked27080 : checkPrefixCuts (2^48) 3553361921 9 Manual.Count131072.C027080.packed 128 cuts27080 = true := by
 decide +kernel
def pointBounds27080 : List (Nat × Nat × Nat) := [(3553412096,103921873951928,103922256541649)]
theorem point_links_checked27080 : (cuts27080.take 1).map (fun c => (3553361921-1+2*2^9*c.k,103921692633064+c.lower,103922075222685+c.upper)) = pointBounds27080 := by
 decide +kernel
def cuts27081 : List PrefixCut := [⟨30,109151968,109152031⟩,
⟨128,471136907,471137173⟩]
theorem checked27081 : checkPrefixCuts (2^48) 3553492993 9 Manual.Count131072.C027081.packed 128 cuts27081 = true := by
 decide +kernel
def pointBounds27081 : List (Nat × Nat × Nat) := [(3553523712,103922274365172,103922656955122)]
theorem point_links_checked27081 : (cuts27081.take 1).map (fun c => (3553492993-1+2*2^9*c.k,103922165213204+c.lower,103922547803091+c.upper)) = pointBounds27081 := by
 decide +kernel
def cuts27082 : List PrefixCut := [⟨11,38574160,38574183⟩,
⟨120,445615541,445615794⟩,
⟨128,473970936,473971206⟩]
theorem checked27082 : checkPrefixCuts (2^48) 3553624065 9 Manual.Count131072.C027082.packed 128 cuts27082 = true := by
 decide +kernel
def pointBounds27082 : List (Nat × Nat × Nat) := [(3553635328,103922674924271,103923057514447),(3553746944,103923081965652,103923464556058)]
theorem point_links_checked27082 : (cuts27082.take 2).map (fun c => (3553624065-1+2*2^9*c.k,103922636350111+c.lower,103923018940264+c.upper)) = pointBounds27082 := by
 decide +kernel
def cuts27083 : List PrefixCut := [⟨101,375109013,375109223⟩,
⟨128,478072014,478072281⟩]
theorem checked27083 : checkPrefixCuts (2^48) 3553755137 9 Manual.Count131072.C027083.packed 128 cuts27083 = true := by
 decide +kernel
def pointBounds27083 : List (Nat × Nat × Nat) := [(3553858560,103923485430060,103923868020693)]
theorem point_links_checked27083 : (cuts27083.take 1).map (fun c => (3553755137-1+2*2^9*c.k,103923110321047+c.lower,103923492911470+c.upper)) = pointBounds27083 := by
 decide +kernel
def cuts27084 : List PrefixCut := [⟨82,299696854,299697024⟩,
⟨128,468233621,468233885⟩]
theorem checked27084 : checkPrefixCuts (2^48) 3553886209 9 Manual.Count131072.C027084.packed 128 cuts27084 = true := by
 decide +kernel
def pointBounds27084 : List (Nat × Nat × Nat) := [(3553970176,103923888089915,103924270680775)]
theorem point_links_checked27084 : (cuts27084.take 1).map (fun c => (3553886209-1+2*2^9*c.k,103923588393061+c.lower,103923970983751+c.upper)) = pointBounds27084 := by
 decide +kernel
def cuts27085 : List PrefixCut := [⟨63,228804049,228804179⟩,
⟨128,474631231,474631497⟩]
theorem checked27085 : checkPrefixCuts (2^48) 3554017281 9 Manual.Count131072.C027085.packed 128 cuts27085 = true := by
 decide +kernel
def pointBounds27085 : List (Nat × Nat × Nat) := [(3554081792,103924285430731,103924668021815)]
theorem point_links_checked27085 : (cuts27085.take 1).map (fun c => (3554017281-1+2*2^9*c.k,103924056626682+c.lower,103924439217636+c.upper)) = pointBounds27085 := by
 decide +kernel
def cuts27086 : List PrefixCut := [⟨44,165994101,165994194⟩,
⟨128,473742761,473743025⟩]
theorem checked27086 : checkPrefixCuts (2^48) 3554148353 9 Manual.Count131072.C027086.packed 128 cuts27086 = true := by
 decide +kernel
def pointBounds27086 : List (Nat × Nat × Nat) := [(3554193408,103924697252014,103925079843327)]
theorem point_links_checked27086 : (cuts27086.take 1).map (fun c => (3554148353-1+2*2^9*c.k,103924531257913+c.lower,103924913849133+c.upper)) = pointBounds27086 := by
 decide +kernel
def cuts27087 : List PrefixCut := [⟨25,91705447,91705499⟩,
⟨128,477209621,477209886⟩]
theorem checked27087 : checkPrefixCuts (2^48) 3554279425 9 Manual.Count131072.C027087.packed 128 cuts27087 = true := by
 decide +kernel
def pointBounds27087 : List (Nat × Nat × Nat) := [(3554305024,103925096706121,103925479297657)]
theorem point_links_checked27087 : (cuts27087.take 1).map (fun c => (3554279425-1+2*2^9*c.k,103925005000674+c.lower,103925387592158+c.upper)) = pointBounds27087 := by
 decide +kernel
def cuts27088 : List PrefixCut := [⟨6,20510275,20510285⟩,
⟨115,425720085,425720325⟩,
⟨128,471886425,471886691⟩]
theorem checked27088 : checkPrefixCuts (2^48) 3554410497 9 Manual.Count131072.C027088.packed 128 cuts27088 = true := by
 decide +kernel
def pointBounds27088 : List (Nat × Nat × Nat) := [(3554416640,103925502720570,103925885312329),(3554528256,103925907930380,103926290522369)]
theorem point_links_checked27088 : (cuts27088.take 2).map (fun c => (3554410497-1+2*2^9*c.k,103925482210295+c.lower,103925864802044+c.upper)) = pointBounds27088 := by
 decide +kernel
def cuts27089 : List PrefixCut := [⟨96,352458255,352458451⟩,
⟨128,471869003,471869265⟩]
theorem checked27089 : checkPrefixCuts (2^48) 3554541569 9 Manual.Count131072.C027089.packed 128 cuts27089 = true := by
 decide +kernel
def pointBounds27089 : List (Nat × Nat × Nat) := [(3554639872,103926306554975,103926689147186)]
theorem point_links_checked27089 : (cuts27089.take 1).map (fun c => (3554541569-1+2*2^9*c.k,103925954096720+c.lower,103926336688735+c.upper)) = pointBounds27089 := by
 decide +kernel
def cuts27090 : List PrefixCut := [⟨77,282606260,282606424⟩,
⟨128,472485005,472485275⟩]
theorem checked27090 : checkPrefixCuts (2^48) 3554672641 9 Manual.Count131072.C027090.packed 128 cuts27090 = true := by
 decide +kernel
def pointBounds27090 : List (Nat × Nat × Nat) := [(3554751488,103926708571983,103927091164424)]
theorem point_links_checked27090 : (cuts27090.take 1).map (fun c => (3554672641-1+2*2^9*c.k,103926425965723+c.lower,103926808558000+c.upper)) = pointBounds27090 := by
 decide +kernel
def cuts27091 : List PrefixCut := [⟨58,212759081,212759205⟩,
⟨128,475397261,475397530⟩]
theorem checked27091 : checkPrefixCuts (2^48) 3554803713 9 Manual.Count131072.C027091.packed 128 cuts27091 = true := by
 decide +kernel
def pointBounds27091 : List (Nat × Nat × Nat) := [(3554863104,103927111209809,103927493802480)]
theorem point_links_checked27091 : (cuts27091.take 1).map (fun c => (3554803713-1+2*2^9*c.k,103926898450728+c.lower,103927281043275+c.upper)) = pointBounds27091 := by
 decide +kernel
def cuts27092 : List PrefixCut := [⟨39,142283207,142283286⟩,
⟨128,472608577,472608843⟩]
theorem checked27092 : checkPrefixCuts (2^48) 3554934785 9 Manual.Count131072.C027092.packed 128 cuts27092 = true := by
 decide +kernel
def pointBounds27092 : List (Nat × Nat × Nat) := [(3554974720,103927516131196,103927898724091)]
theorem point_links_checked27092 : (cuts27092.take 1).map (fun c => (3554934785-1+2*2^9*c.k,103927373847989+c.lower,103927756440805+c.upper)) = pointBounds27092 := by
 decide +kernel
def cuts27093 : List PrefixCut := [⟨20,71337120,71337159⟩,
⟨128,469899205,469899466⟩]
theorem checked27093 : checkPrefixCuts (2^48) 3555065857 9 Manual.Count131072.C027093.packed 128 cuts27093 = true := by
 decide +kernel
def pointBounds27093 : List (Nat × Nat × Nat) := [(3555086336,103927917793686,103928300386807)]
theorem point_links_checked27093 : (cuts27093.take 1).map (fun c => (3555065857-1+2*2^9*c.k,103927846456566+c.lower,103928229049648+c.upper)) = pointBounds27093 := by
 decide +kernel
def cuts27094 : List PrefixCut := [⟨1,3641948,3641950⟩,
⟨110,406704173,406704407⟩,
⟨128,472969533,472969807⟩]
theorem checked27094 : checkPrefixCuts (2^48) 3555196929 9 Manual.Count131072.C027094.packed 128 cuts27094 = true := by
 decide +kernel
def pointBounds27094 : List (Nat × Nat × Nat) := [(3555197952,103928319997719,103928702591064),(3555309568,103928723059944,103929105653521)]
theorem point_links_checked27094 : (cuts27094.take 2).map (fun c => (3555196929-1+2*2^9*c.k,103928316355771+c.lower,103928698949114+c.upper)) = pointBounds27094 := by
 decide +kernel
def cuts27095 : List PrefixCut := [⟨91,336071743,336071930⟩,
⟨128,477464701,477464966⟩]
theorem checked27095 : checkPrefixCuts (2^48) 3555328001 9 Manual.Count131072.C027095.packed 128 cuts27095 = true := by
 decide +kernel
def pointBounds27095 : List (Nat × Nat × Nat) := [(3555421184,103929125397047,103929507990851)]
theorem point_links_checked27095 : (cuts27095.take 1).map (fun c => (3555328001-1+2*2^9*c.k,103928789325304+c.lower,103929171918921+c.upper)) = pointBounds27095 := by
 decide +kernel
def cuts27096 : List PrefixCut := [⟨72,265681543,265681697⟩,
⟨128,471588889,471589158⟩]
theorem checked27096 : checkPrefixCuts (2^48) 3555459073 9 Manual.Count131072.C027096.packed 128 cuts27096 = true := by
 decide +kernel
def pointBounds27096 : List (Nat × Nat × Nat) := [(3555532800,103929532471548,103929915065584)]
theorem point_links_checked27096 : (cuts27096.take 1).map (fun c => (3555459073-1+2*2^9*c.k,103929266790005+c.lower,103929649383887+c.upper)) = pointBounds27096 := by
 decide +kernel
def cuts27097 : List PrefixCut := [⟨53,194425415,194425524⟩,
⟨128,473313052,473313315⟩]
theorem checked27097 : checkPrefixCuts (2^48) 3555590145 9 Manual.Count131072.C027097.packed 128 cuts27097 = true := by
 decide +kernel
def pointBounds27097 : List (Nat × Nat × Nat) := [(3555644416,103929932804309,103930315398569)]
theorem point_links_checked27097 : (cuts27097.take 1).map (fun c => (3555590145-1+2*2^9*c.k,103929738378894+c.lower,103930120973045+c.upper)) = pointBounds27097 := by
 decide +kernel
def cuts27098 : List PrefixCut := [⟨34,123886564,123886632⟩,
⟨128,465854646,465854905⟩]
theorem checked27098 : checkPrefixCuts (2^48) 3555721217 9 Manual.Count131072.C027098.packed 128 cuts27098 = true := by
 decide +kernel
def pointBounds27098 : List (Nat × Nat × Nat) := [(3555756032,103930335578510,103930718172992)]
theorem point_links_checked27098 : (cuts27098.take 1).map (fun c => (3555721217-1+2*2^9*c.k,103930211691946+c.lower,103930594286360+c.upper)) = pointBounds27098 := by
 decide +kernel
def cuts27099 : List PrefixCut := [⟨15,55093998,55094031⟩,
⟨124,456338918,456339173⟩,
⟨128,472249141,472249405⟩]
theorem checked27099 : checkPrefixCuts (2^48) 3555852289 9 Manual.Count131072.C027099.packed 128 cuts27099 = true := by
 decide +kernel
def pointBounds27099 : List (Nat × Nat × Nat) := [(3555867648,103930732640590,103931115235296),(3555979264,103931133885510,103931516480438)]
theorem point_links_checked27099 : (cuts27099.take 2).map (fun c => (3555852289-1+2*2^9*c.k,103930677546592+c.lower,103931060141265+c.upper)) = pointBounds27099 := by
 decide +kernel
def cuts27100 : List PrefixCut := [⟨105,390625508,390625723⟩,
⟨128,478247474,478247737⟩]
theorem checked27100 : checkPrefixCuts (2^48) 3555983361 9 Manual.Count131072.C027100.packed 128 cuts27100 = true := by
 decide +kernel
def pointBounds27100 : List (Nat × Nat × Nat) := [(3556090880,103931540421241,103931923016393)]
theorem point_links_checked27100 : (cuts27100.take 1).map (fun c => (3555983361-1+2*2^9*c.k,103931149795733+c.lower,103931532390670+c.upper)) = pointBounds27100 := by
 decide +kernel
def cuts27101 : List PrefixCut := [⟨86,315418304,315418485⟩,
⟨128,471660283,471660551⟩]
theorem checked27101 : checkPrefixCuts (2^48) 3556114433 9 Manual.Count131072.C027101.packed 128 cuts27101 = true := by
 decide +kernel
def pointBounds27101 : List (Nat × Nat × Nat) := [(3556202496,103931943461511,103932326056892)]
theorem point_links_checked27101 : (cuts27101.take 1).map (fun c => (3556114433-1+2*2^9*c.k,103931628043207+c.lower,103932010638407+c.upper)) = pointBounds27101 := by
 decide +kernel
def cuts27102 : List PrefixCut := [⟨67,248922616,248922757⟩,
⟨128,475283673,475283941⟩]
theorem checked27102 : checkPrefixCuts (2^48) 3556245505 9 Manual.Count131072.C027102.packed 128 cuts27102 = true := by
 decide +kernel
def pointBounds27102 : List (Nat × Nat × Nat) := [(3556314112,103932348626106,103932731221715)]
theorem point_links_checked27102 : (cuts27102.take 1).map (fun c => (3556245505-1+2*2^9*c.k,103932099703490+c.lower,103932482298958+c.upper)) = pointBounds27102 := by
 decide +kernel
def cuts27103 : List PrefixCut := [⟨48,175545802,175545899⟩,
⟨128,468459699,468459957⟩]
theorem checked27103 : checkPrefixCuts (2^48) 3556376577 9 Manual.Count131072.C027103.packed 128 cuts27103 = true := by
 decide +kernel
def pointBounds27103 : List (Nat × Nat × Nat) := [(3556425728,103932750532965,103933133128798)]
theorem point_links_checked27103 : (cuts27103.take 1).map (fun c => (3556376577-1+2*2^9*c.k,103932574987163+c.lower,103932957582899+c.upper)) = pointBounds27103 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000221
