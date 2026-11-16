import PlattAssemblyKernel
import PlattCertificates.Count131072.C049120
import PlattCertificates.Count131072.C049121
import PlattCertificates.Count131072.C049122
import PlattCertificates.Count131072.C049123
import PlattCertificates.Count131072.C049124
import PlattCertificates.Count131072.C049125
import PlattCertificates.Count131072.C049126
import PlattCertificates.Count131072.C049127
import PlattCertificates.Count131072.C049128
import PlattCertificates.Count131072.C049129
import PlattCertificates.Count131072.C049130
import PlattCertificates.Count131072.C049131
import PlattCertificates.Count131072.C049132
import PlattCertificates.Count131072.C049133
import PlattCertificates.Count131072.C049134
import PlattCertificates.Count131072.C049135
import PlattCertificates.Count131072.C049136
import PlattCertificates.Count131072.C049137
import PlattCertificates.Count131072.C049138
import PlattCertificates.Count131072.C049139
import PlattCertificates.Count131072.C049140
import PlattCertificates.Count131072.C049141
import PlattCertificates.Count131072.C049142
import PlattCertificates.Count131072.C049143
import PlattCertificates.Count131072.C049144
import PlattCertificates.Count131072.C049145
import PlattCertificates.Count131072.C049146
import PlattCertificates.Count131072.C049147
import PlattCertificates.Count131072.C049148
import PlattCertificates.Count131072.C049149
import PlattCertificates.Count131072.C049150
import PlattCertificates.Count131072.C049151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000285
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49120 : List PrefixCut := [⟨41,160306493,160306583⟩,
⟨64,252539679,252539826⟩]
theorem checked49120 : checkPrefixCuts (2^48) 6442188801 10 Manual.Count131072.C049120.packed 64 cuts49120 = true := by
 decide +kernel
def pointBounds49120 : List (Nat × Nat × Nat) := [(6442272768,111435904649674,111436291645794)]
theorem point_links_checked49120 : (cuts49120.take 1).map (fun c => (6442188801-1+2*2^10*c.k,111435744343181+c.lower,111436131339211+c.upper)) = pointBounds49120 := by
 decide +kernel
def cuts49121 : List PrefixCut := [⟨64,255724002,255724145⟩]
theorem checked49121 : checkPrefixCuts (2^48) 6442319873 10 Manual.Count131072.C049121.packed 64 cuts49121 = true := by
 decide +kernel
def cuts49122 : List PrefixCut := [⟨12,46268315,46268342⟩,
⟨64,253534293,253534437⟩]
theorem checked49122 : checkPrefixCuts (2^48) 6442450945 10 Manual.Count131072.C049122.packed 64 cuts49122 = true := by
 decide +kernel
def pointBounds49122 : List (Nat × Nat × Nat) := [(6442475520,111436298875177,111436685871524)]
theorem point_links_checked49122 : (cuts49122.take 1).map (fun c => (6442450945-1+2*2^10*c.k,111436252606862+c.lower,111436639603182+c.upper)) = pointBounds49122 := by
 decide +kernel
def cuts49123 : List PrefixCut := [⟨47,188301475,188301580⟩,
⟨64,256456309,256456452⟩]
theorem checked49123 : checkPrefixCuts (2^48) 6442582017 10 Manual.Count131072.C049123.packed 64 cuts49123 = true := by
 decide +kernel
def pointBounds49123 : List (Nat × Nat × Nat) := [(6442678272,111436694442630,111437081439199)]
theorem point_links_checked49123 : (cuts49123.take 1).map (fun c => (6442582017-1+2*2^10*c.k,111436506141155+c.lower,111436893137619+c.upper)) = pointBounds49123 := by
 decide +kernel
def cuts49124 : List PrefixCut := [⟨64,253349215,253349367⟩]
theorem checked49124 : checkPrefixCuts (2^48) 6442713089 10 Manual.Count131072.C049124.packed 64 cuts49124 = true := by
 decide +kernel
def cuts49125 : List PrefixCut := [⟨18,70468523,70468565⟩,
⟨64,250198561,250198705⟩]
theorem checked49125 : checkPrefixCuts (2^48) 6442844161 10 Manual.Count131072.C049125.packed 64 cuts49125 = true := by
 decide +kernel
def pointBounds49125 : List (Nat × Nat × Nat) := [(6442881024,111437086415202,111437473412003)]
theorem point_links_checked49125 : (cuts49125.take 1).map (fun c => (6442844161-1+2*2^10*c.k,111437015946679+c.lower,111437402943438+c.upper)) = pointBounds49125 := by
 decide +kernel
def cuts49126 : List PrefixCut := [⟨53,209477871,209477991⟩,
⟨64,252203059,252203202⟩]
theorem checked49126 : checkPrefixCuts (2^48) 6442975233 10 Manual.Count131072.C049126.packed 64 cuts49126 = true := by
 decide +kernel
def pointBounds49126 : List (Nat × Nat × Nat) := [(6443083776,111437475623111,111437862620134)]
theorem point_links_checked49126 : (cuts49126.take 1).map (fun c => (6442975233-1+2*2^10*c.k,111437266145240+c.lower,111437653142143+c.upper)) = pointBounds49126 := by
 decide +kernel
def cuts49127 : List PrefixCut := [⟨64,256173316,256173465⟩]
theorem checked49127 : checkPrefixCuts (2^48) 6443106305 10 Manual.Count131072.C049127.packed 64 cuts49127 = true := by
 decide +kernel
def cuts49128 : List PrefixCut := [⟨24,98641084,98641140⟩,
⟨64,256954478,256954625⟩]
theorem checked49128 : checkPrefixCuts (2^48) 6443237377 10 Manual.Count131072.C049128.packed 64 cuts49128 = true := by
 decide +kernel
def pointBounds49128 : List (Nat × Nat × Nat) := [(6443286528,111437873162699,111438260159950)]
theorem point_links_checked49128 : (cuts49128.take 1).map (fun c => (6443237377-1+2*2^10*c.k,111437774521615+c.lower,111438161518810+c.upper)) = pointBounds49128 := by
 decide +kernel
def cuts49129 : List PrefixCut := [⟨59,230520585,230520713⟩,
⟨64,249610309,249610447⟩]
theorem checked49129 : checkPrefixCuts (2^48) 6443368449 10 Manual.Count131072.C049129.packed 64 cuts49129 = true := by
 decide +kernel
def pointBounds49129 : List (Nat × Nat × Nat) := [(6443489280,111438261996678,111438648994148)]
theorem point_links_checked49129 : (cuts49129.take 1).map (fun c => (6443368449-1+2*2^10*c.k,111438031476093+c.lower,111438418473435+c.upper)) = pointBounds49129 := by
 decide +kernel
def cuts49130 : List PrefixCut := [⟨64,254104583,254104728⟩]
theorem checked49130 : checkPrefixCuts (2^48) 6443499521 10 Manual.Count131072.C049130.packed 64 cuts49130 = true := by
 decide +kernel
def cuts49131 : List PrefixCut := [⟨30,116850551,116850619⟩,
⟨64,252701586,252701731⟩]
theorem checked49131 : checkPrefixCuts (2^48) 6443630593 10 Manual.Count131072.C049131.packed 64 cuts49131 = true := by
 decide +kernel
def pointBounds49131 : List (Nat × Nat × Nat) := [(6443692032,111438652041536,111439039039229)]
theorem point_links_checked49131 : (cuts49131.take 1).map (fun c => (6443630593-1+2*2^10*c.k,111438535190985+c.lower,111438922188610+c.upper)) = pointBounds49131 := by
 decide +kernel
def cuts49132 : List PrefixCut := [⟨64,252041214,252041357⟩]
theorem checked49132 : checkPrefixCuts (2^48) 6443761665 10 Manual.Count131072.C049132.packed 64 cuts49132 = true := by
 decide +kernel
def cuts49133 : List PrefixCut := [⟨1,3800236,3800238⟩,
⟨64,253914374,253914523⟩]
theorem checked49133 : checkPrefixCuts (2^48) 6443892737 10 Manual.Count131072.C049133.packed 64 cuts49133 = true := by
 decide +kernel
def pointBounds49133 : List (Nat × Nat × Nat) := [(6443894784,111439043734021,111439430731936)]
theorem point_links_checked49133 : (cuts49133.take 1).map (fun c => (6443892737-1+2*2^10*c.k,111439039933785+c.lower,111439426931698+c.upper)) = pointBounds49133 := by
 decide +kernel
def cuts49134 : List PrefixCut := [⟨36,144099466,144099549⟩,
⟨64,251899971,251900115⟩]
theorem checked49134 : checkPrefixCuts (2^48) 6444023809 10 Manual.Count131072.C049134.packed 64 cuts49134 = true := by
 decide +kernel
def pointBounds49134 : List (Nat × Nat × Nat) := [(6444097536,111439437947625,111439824945770)]
theorem point_links_checked49134 : (cuts49134.take 1).map (fun c => (6444023809-1+2*2^10*c.k,111439293848159+c.lower,111439680846221+c.upper)) = pointBounds49134 := by
 decide +kernel
def cuts49135 : List PrefixCut := [⟨64,253904031,253904177⟩]
theorem checked49135 : checkPrefixCuts (2^48) 6444154881 10 Manual.Count131072.C049135.packed 64 cuts49135 = true := by
 decide +kernel
def cuts49136 : List PrefixCut := [⟨7,28696554,28696570⟩,
⟨64,256170121,256170270⟩]
theorem checked49136 : checkPrefixCuts (2^48) 6444285953 10 Manual.Count131072.C049136.packed 64 cuts49136 = true := by
 decide +kernel
def pointBounds49136 : List (Nat × Nat × Nat) := [(6444300288,111439828348715,111440215347083)]
theorem point_links_checked49136 : (cuts49136.take 1).map (fun c => (6444285953-1+2*2^10*c.k,111439799652161+c.lower,111440186650513+c.upper)) = pointBounds49136 := by
 decide +kernel
def cuts49137 : List PrefixCut := [⟨42,165972730,165972824⟩,
⟨64,254286794,254286936⟩]
theorem checked49137 : checkPrefixCuts (2^48) 6444417025 10 Manual.Count131072.C049137.packed 64 cuts49137 = true := by
 decide +kernel
def pointBounds49137 : List (Nat × Nat × Nat) := [(6444503040,111440221795012,111440608793607)]
theorem point_links_checked49137 : (cuts49137.take 1).map (fun c => (6444417025-1+2*2^10*c.k,111440055822282+c.lower,111440442820783+c.upper)) = pointBounds49137 := by
 decide +kernel
def cuts49138 : List PrefixCut := [⟨64,253058695,253058841⟩]
theorem checked49138 : checkPrefixCuts (2^48) 6444548097 10 Manual.Count131072.C049138.packed 64 cuts49138 = true := by
 decide +kernel
def cuts49139 : List PrefixCut := [⟨13,51449688,51449716⟩,
⟨64,252616817,252616958⟩]
theorem checked49139 : checkPrefixCuts (2^48) 6444679169 10 Manual.Count131072.C049139.packed 64 cuts49139 = true := by
 decide +kernel
def pointBounds49139 : List (Nat × Nat × Nat) := [(6444705792,111440614617459,111441001616276)]
theorem point_links_checked49139 : (cuts49139.take 1).map (fun c => (6444679169-1+2*2^10*c.k,111440563167771+c.lower,111440950166560+c.upper)) = pointBounds49139 := by
 decide +kernel
def cuts49140 : List PrefixCut := [⟨48,192210729,192210835⟩,
⟨64,256105620,256105762⟩]
theorem checked49140 : checkPrefixCuts (2^48) 6444810241 10 Manual.Count131072.C049140.packed 64 cuts49140 = true := by
 decide +kernel
def pointBounds49140 : List (Nat × Nat × Nat) := [(6444908544,111441007995317,111441394994353)]
theorem point_links_checked49140 : (cuts49140.take 1).map (fun c => (6444810241-1+2*2^10*c.k,111440815784588+c.lower,111441202783518+c.upper)) = pointBounds49140 := by
 decide +kernel
def cuts49141 : List PrefixCut := [⟨64,252562841,252562984⟩]
theorem checked49141 : checkPrefixCuts (2^48) 6444941313 10 Manual.Count131072.C049141.packed 64 cuts49141 = true := by
 decide +kernel
def cuts49142 : List PrefixCut := [⟨19,76077936,76077980⟩,
⟨64,255352746,255352900⟩]
theorem checked49142 : checkPrefixCuts (2^48) 6445072385 10 Manual.Count131072.C049142.packed 64 cuts49142 = true := by
 decide +kernel
def pointBounds49142 : List (Nat × Nat × Nat) := [(6445111296,111441400530985,111441787530244)]
theorem point_links_checked49142 : (cuts49142.take 1).map (fun c => (6445072385-1+2*2^10*c.k,111441324453049+c.lower,111441711452264+c.upper)) = pointBounds49142 := by
 decide +kernel
def cuts49143 : List PrefixCut := [⟨54,216174523,216174650⟩,
⟨64,255827954,255828102⟩]
theorem checked49143 : checkPrefixCuts (2^48) 6445203457 10 Manual.Count131072.C049143.packed 64 cuts49143 = true := by
 decide +kernel
def pointBounds49143 : List (Nat × Nat × Nat) := [(6445314048,111441795980318,111442182979814)]
theorem point_links_checked49143 : (cuts49143.take 1).map (fun c => (6445203457-1+2*2^10*c.k,111441579805795+c.lower,111441966805164+c.upper)) = pointBounds49143 := by
 decide +kernel
def cuts49144 : List PrefixCut := [⟨64,251062654,251062796⟩]
theorem checked49144 : checkPrefixCuts (2^48) 6445334529 10 Manual.Count131072.C049144.packed 64 cuts49144 = true := by
 decide +kernel
def cuts49145 : List PrefixCut := [⟨25,98650638,98650693⟩,
⟨64,252018272,252018413⟩]
theorem checked49145 : checkPrefixCuts (2^48) 6445465601 10 Manual.Count131072.C049145.packed 64 cuts49145 = true := by
 decide +kernel
def pointBounds49145 : List (Nat × Nat × Nat) := [(6445516800,111442185347041,111442572346755)]
theorem point_links_checked49145 : (cuts49145.take 1).map (fun c => (6445465601-1+2*2^10*c.k,111442086696403+c.lower,111442473696062+c.upper)) = pointBounds49145 := by
 decide +kernel
def cuts49146 : List PrefixCut := [⟨60,236729202,236729344⟩,
⟨64,252842868,252843019⟩]
theorem checked49146 : checkPrefixCuts (2^48) 6445596673 10 Manual.Count131072.C049146.packed 64 cuts49146 = true := by
 decide +kernel
def pointBounds49146 : List (Nat × Nat × Nat) := [(6445719552,111442575443877,111442962443819)]
theorem point_links_checked49146 : (cuts49146.take 1).map (fun c => (6445596673-1+2*2^10*c.k,111442338714675+c.lower,111442725714475+c.upper)) = pointBounds49146 := by
 decide +kernel
def cuts49147 : List PrefixCut := [⟨64,254933753,254933894⟩]
theorem checked49147 : checkPrefixCuts (2^48) 6445727745 10 Manual.Count131072.C049147.packed 64 cuts49147 = true := by
 decide +kernel
def cuts49148 : List PrefixCut := [⟨31,122224887,122224953⟩,
⟨64,253793243,253793383⟩]
theorem checked49148 : checkPrefixCuts (2^48) 6445858817 10 Manual.Count131072.C049148.packed 64 cuts49148 = true := by
 decide +kernel
def pointBounds49148 : List (Nat × Nat × Nat) := [(6445922304,111442968716183,111443355716341)]
theorem point_links_checked49148 : (cuts49148.take 1).map (fun c => (6445858817-1+2*2^10*c.k,111442846491296+c.lower,111443233491388+c.upper)) = pointBounds49148 := by
 decide +kernel
def cuts49149 : List PrefixCut := [⟨64,251473786,251473940⟩]
theorem checked49149 : checkPrefixCuts (2^48) 6445989889 10 Manual.Count131072.C049149.packed 64 cuts49149 = true := by
 decide +kernel
def cuts49150 : List PrefixCut := [⟨2,8078167,8078171⟩,
⟨64,253040614,253040756⟩]
theorem checked49150 : checkPrefixCuts (2^48) 6446120961 10 Manual.Count131072.C049150.packed 64 cuts49150 = true := by
 decide +kernel
def pointBounds49150 : List (Nat × Nat × Nat) := [(6446125056,111443359836492,111443746836882)]
theorem point_links_checked49150 : (cuts49150.take 1).map (fun c => (6446120961-1+2*2^10*c.k,111443351758325+c.lower,111443738758711+c.upper)) = pointBounds49150 := by
 decide +kernel
def cuts49151 : List PrefixCut := [⟨37,149769693,149769782⟩,
⟨64,257183608,257183758⟩]
theorem checked49151 : checkPrefixCuts (2^48) 6446252033 10 Manual.Count131072.C049151.packed 64 cuts49151 = true := by
 decide +kernel
def pointBounds49151 : List (Nat × Nat × Nat) := [(6446327808,111443754568632,111444141569249)]
theorem point_links_checked49151 : (cuts49151.take 1).map (fun c => (6446252033-1+2*2^10*c.k,111443604798939+c.lower,111443991799467+c.upper)) = pointBounds49151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000285
