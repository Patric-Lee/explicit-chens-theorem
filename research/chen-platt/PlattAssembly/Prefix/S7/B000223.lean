import PlattAssemblyKernel
import PlattCertificates.Count131072.C067136
import PlattCertificates.Count131072.C067137
import PlattCertificates.Count131072.C067138
import PlattCertificates.Count131072.C067139
import PlattCertificates.Count131072.C067140
import PlattCertificates.Count131072.C067141
import PlattCertificates.Count131072.C067142
import PlattCertificates.Count131072.C067143
import PlattCertificates.Count131072.C067144
import PlattCertificates.Count131072.C067145
import PlattCertificates.Count131072.C067146
import PlattCertificates.Count131072.C067147
import PlattCertificates.Count131072.C067148
import PlattCertificates.Count131072.C067149
import PlattCertificates.Count131072.C067150
import PlattCertificates.Count131072.C067151
import PlattCertificates.Count131072.C067152
import PlattCertificates.Count131072.C067153
import PlattCertificates.Count131072.C067154
import PlattCertificates.Count131072.C067155
import PlattCertificates.Count131072.C067156
import PlattCertificates.Count131072.C067157
import PlattCertificates.Count131072.C067158
import PlattCertificates.Count131072.C067159
import PlattCertificates.Count131072.C067160
import PlattCertificates.Count131072.C067161
import PlattCertificates.Count131072.C067162
import PlattCertificates.Count131072.C067163
import PlattCertificates.Count131072.C067164
import PlattCertificates.Count131072.C067165
import PlattCertificates.Count131072.C067166
import PlattCertificates.Count131072.C067167
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000223
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67136 : List PrefixCut := [⟨44,127027166,127027238⟩,
⟨64,186048156,186048262⟩]
theorem checked67136 : checkPrefixCuts (2^48) 8803581953 10 Manual.Count131072.C067136.packed 64 cuts67136 = true := by
 decide +kernel
def pointBounds67136 : List (Nat × Nat × Nat) := [(8803672064,115301067430156,115301456635094)]
theorem point_links_checked67136 : (cuts67136.take 1).map (fun c => (8803581953-1+2*2^10*c.k,115300940402990+c.lower,115301329607856+c.upper)) = pointBounds67136 := by
 decide +kernel
def cuts67137 : List PrefixCut := [⟨64,181089717,181089825⟩]
theorem checked67137 : checkPrefixCuts (2^48) 8803713025 10 Manual.Count131072.C067137.packed 64 cuts67137 = true := by
 decide +kernel
def cuts67138 : List PrefixCut := [⟨51,144639637,144639717⟩,
⟨64,180991105,180991209⟩]
theorem checked67138 : checkPrefixCuts (2^48) 8803844097 10 Manual.Count131072.C067138.packed 64 cuts67138 = true := by
 decide +kernel
def pointBounds67138 : List (Nat × Nat × Nat) := [(8803948544,115301452180500,115301841385660)]
theorem point_links_checked67138 : (cuts67138.take 1).map (fun c => (8803844097-1+2*2^10*c.k,115301307540863+c.lower,115301696745943+c.upper)) = pointBounds67138 := by
 decide +kernel
def cuts67139 : List PrefixCut := [⟨64,182011479,182011587⟩]
theorem checked67139 : checkPrefixCuts (2^48) 8803975169 10 Manual.Count131072.C067139.packed 64 cuts67139 = true := by
 decide +kernel
def cuts67140 : List PrefixCut := [⟨58,166982706,166982802⟩,
⟨64,183863082,183863189⟩]
theorem checked67140 : checkPrefixCuts (2^48) 8804106241 10 Manual.Count131072.C067140.packed 64 cuts67140 = true := by
 decide +kernel
def pointBounds67140 : List (Nat × Nat × Nat) := [(8804225024,115301837526153,115302226731541)]
theorem point_links_checked67140 : (cuts67140.take 1).map (fun c => (8804106241-1+2*2^10*c.k,115301670543447+c.lower,115302059748739+c.upper)) = pointBounds67140 := by
 decide +kernel
def cuts67141 : List PrefixCut := [⟨64,182357739,182357844⟩]
theorem checked67141 : checkPrefixCuts (2^48) 8804237313 10 Manual.Count131072.C067141.packed 64 cuts67141 = true := by
 decide +kernel
def cuts67142 : List PrefixCut := [⟨64,184113346,184113457⟩]
theorem checked67142 : checkPrefixCuts (2^48) 8804368385 10 Manual.Count131072.C067142.packed 64 cuts67142 = true := by
 decide +kernel
def cuts67143 : List PrefixCut := [⟨1,2941188,2941190⟩,
⟨64,182576106,182576208⟩]
theorem checked67143 : checkPrefixCuts (2^48) 8804499457 10 Manual.Count131072.C067143.packed 64 cuts67143 = true := by
 decide +kernel
def pointBounds67143 : List (Nat × Nat × Nat) := [(8804501504,115302223818802,115302613024419)]
theorem point_links_checked67143 : (cuts67143.take 1).map (fun c => (8804499457-1+2*2^10*c.k,115302220877614+c.lower,115302610083229+c.upper)) = pointBounds67143 := by
 decide +kernel
def cuts67144 : List PrefixCut := [⟨64,185002997,185003100⟩]
theorem checked67144 : checkPrefixCuts (2^48) 8804630529 10 Manual.Count131072.C067144.packed 64 cuts67144 = true := by
 decide +kernel
def cuts67145 : List PrefixCut := [⟨8,22633667,22633679⟩,
⟨64,184424818,184424920⟩]
theorem checked67145 : checkPrefixCuts (2^48) 8804761601 10 Manual.Count131072.C067145.packed 64 cuts67145 = true := by
 decide +kernel
def pointBounds67145 : List (Nat × Nat × Nat) := [(8804777984,115302611090384,115303000296216)]
theorem point_links_checked67145 : (cuts67145.take 1).map (fun c => (8804761601-1+2*2^10*c.k,115302588456717+c.lower,115302977662537+c.upper)) = pointBounds67145 := by
 decide +kernel
def cuts67146 : List PrefixCut := [⟨64,184422076,184422187⟩]
theorem checked67146 : checkPrefixCuts (2^48) 8804892673 10 Manual.Count131072.C067146.packed 64 cuts67146 = true := by
 decide +kernel
def cuts67147 : List PrefixCut := [⟨15,42261006,42261033⟩,
⟨64,182916859,182916972⟩]
theorem checked67147 : checkPrefixCuts (2^48) 8805023745 10 Manual.Count131072.C067147.packed 64 cuts67147 = true := by
 decide +kernel
def pointBounds67147 : List (Nat × Nat × Nat) := [(8805054464,115302999564617,115303388770677)]
theorem point_links_checked67147 : (cuts67147.take 1).map (fun c => (8805023745-1+2*2^10*c.k,115302957303611+c.lower,115303346509644+c.upper)) = pointBounds67147 := by
 decide +kernel
def cuts67148 : List PrefixCut := [⟨64,180900234,180900339⟩]
theorem checked67148 : checkPrefixCuts (2^48) 8805154817 10 Manual.Count131072.C067148.packed 64 cuts67148 = true := by
 decide +kernel
def cuts67149 : List PrefixCut := [⟨22,63293671,63293706⟩,
⟨64,184445795,184445903⟩]
theorem checked67149 : checkPrefixCuts (2^48) 8805285889 10 Manual.Count131072.C067149.packed 64 cuts67149 = true := by
 decide +kernel
def pointBounds67149 : List (Nat × Nat × Nat) := [(8805330944,115303384414375,115303773620661)]
theorem point_links_checked67149 : (cuts67149.take 1).map (fun c => (8805285889-1+2*2^10*c.k,115303321120704+c.lower,115303710326955+c.upper)) = pointBounds67149 := by
 decide +kernel
def cuts67150 : List PrefixCut := [⟨64,182557076,182557179⟩]
theorem checked67150 : checkPrefixCuts (2^48) 8805416961 10 Manual.Count131072.C067150.packed 64 cuts67150 = true := by
 decide +kernel
def cuts67151 : List PrefixCut := [⟨29,83621803,83621854⟩,
⟨64,184344414,184344525⟩]
theorem checked67151 : checkPrefixCuts (2^48) 8805548033 10 Manual.Count131072.C067151.packed 64 cuts67151 = true := by
 decide +kernel
def pointBounds67151 : List (Nat × Nat × Nat) := [(8805607424,115303771745378,115304160951891)]
theorem point_links_checked67151 : (cuts67151.take 1).map (fun c => (8805548033-1+2*2^10*c.k,115303688123575+c.lower,115304077330037+c.upper)) = pointBounds67151 := by
 decide +kernel
def cuts67152 : List PrefixCut := [⟨64,182136100,182136203⟩]
theorem checked67152 : checkPrefixCuts (2^48) 8805679105 10 Manual.Count131072.C067152.packed 64 cuts67152 = true := by
 decide +kernel
def cuts67153 : List PrefixCut := [⟨36,102222611,102222676⟩,
⟨64,182261237,182261344⟩]
theorem checked67153 : checkPrefixCuts (2^48) 8805810177 10 Manual.Count131072.C067153.packed 64 cuts67153 = true := by
 decide +kernel
def pointBounds67153 : List (Nat × Nat × Nat) := [(8805883904,115304156826700,115304546033441)]
theorem point_links_checked67153 : (cuts67153.take 1).map (fun c => (8805810177-1+2*2^10*c.k,115304054604089+c.lower,115304443810765+c.upper)) = pointBounds67153 := by
 decide +kernel
def cuts67154 : List PrefixCut := [⟨64,182482271,182482372⟩]
theorem checked67154 : checkPrefixCuts (2^48) 8805941249 10 Manual.Count131072.C067154.packed 64 cuts67154 = true := by
 decide +kernel
def cuts67155 : List PrefixCut := [⟨43,124338277,124338346⟩,
⟨64,185132529,185132635⟩]
theorem checked67155 : checkPrefixCuts (2^48) 8806072321 10 Manual.Count131072.C067155.packed 64 cuts67155 = true := by
 decide +kernel
def pointBounds67155 : List (Nat × Nat × Nat) := [(8806160384,115304543685874,115304932892827)]
theorem point_links_checked67155 : (cuts67155.take 1).map (fun c => (8806072321-1+2*2^10*c.k,115304419347597+c.lower,115304808554481+c.upper)) = pointBounds67155 := by
 decide +kernel
def cuts67156 : List PrefixCut := [⟨64,181677762,181677869⟩]
theorem checked67156 : checkPrefixCuts (2^48) 8806203393 10 Manual.Count131072.C067156.packed 64 cuts67156 = true := by
 decide +kernel
def cuts67157 : List PrefixCut := [⟨50,144311105,144311189⟩,
⟨64,185638426,185638535⟩]
theorem checked67157 : checkPrefixCuts (2^48) 8806334465 10 Manual.Count131072.C067157.packed 64 cuts67157 = true := by
 decide +kernel
def pointBounds67157 : List (Nat × Nat × Nat) := [(8806436864,115304930468993,115305319676174)]
theorem point_links_checked67157 : (cuts67157.take 1).map (fun c => (8806334465-1+2*2^10*c.k,115304786157888+c.lower,115305175364985+c.upper)) = pointBounds67157 := by
 decide +kernel
def cuts67158 : List PrefixCut := [⟨64,182279640,182279747⟩]
theorem checked67158 : checkPrefixCuts (2^48) 8806465537 10 Manual.Count131072.C067158.packed 64 cuts67158 = true := by
 decide +kernel
def cuts67159 : List PrefixCut := [⟨57,165273499,165273593⟩,
⟨64,185760742,185760847⟩]
theorem checked67159 : checkPrefixCuts (2^48) 8806596609 10 Manual.Count131072.C067159.packed 64 cuts67159 = true := by
 decide +kernel
def pointBounds67159 : List (Nat × Nat × Nat) := [(8806713344,115305319349453,115305708556860)]
theorem point_links_checked67159 : (cuts67159.take 1).map (fun c => (8806596609-1+2*2^10*c.k,115305154075954+c.lower,115305543283267+c.upper)) = pointBounds67159 := by
 decide +kernel
def cuts67160 : List PrefixCut := [⟨64,183424811,183424918⟩]
theorem checked67160 : checkPrefixCuts (2^48) 8806727681 10 Manual.Count131072.C067160.packed 64 cuts67160 = true := by
 decide +kernel
def cuts67161 : List PrefixCut := [⟨64,178596020,178596131⟩]
theorem checked67161 : checkPrefixCuts (2^48) 8806858753 10 Manual.Count131072.C067161.packed 64 cuts67161 = true := by
 decide +kernel
def pointBounds67161 : List (Nat × Nat × Nat) := [(8806989824,115305701857527,115306091065163)]
theorem point_links_checked67161 : (cuts67161.take 1).map (fun c => (8806858753-1+2*2^10*c.k,115305523261507+c.lower,115305912469032+c.upper)) = pointBounds67161 := by
 decide +kernel
def cuts67162 : List PrefixCut := [⟨64,183323473,183323582⟩]
theorem checked67162 : checkPrefixCuts (2^48) 8806989825 10 Manual.Count131072.C067162.packed 64 cuts67162 = true := by
 decide +kernel
def cuts67163 : List PrefixCut := [⟨64,183160947,183161053⟩]
theorem checked67163 : checkPrefixCuts (2^48) 8807120897 10 Manual.Count131072.C067163.packed 64 cuts67163 = true := by
 decide +kernel
def cuts67164 : List PrefixCut := [⟨7,19367408,19367421⟩,
⟨64,181560248,181560363⟩]
theorem checked67164 : checkPrefixCuts (2^48) 8807251969 10 Manual.Count131072.C067164.packed 64 cuts67164 = true := by
 decide +kernel
def pointBounds67164 : List (Nat × Nat × Nat) := [(8807266304,115306087709355,115306476917219)]
theorem point_links_checked67164 : (cuts67164.take 1).map (fun c => (8807251969-1+2*2^10*c.k,115306068341947+c.lower,115306457549798+c.upper)) = pointBounds67164 := by
 decide +kernel
def cuts67165 : List PrefixCut := [⟨64,182100852,182100953⟩]
theorem checked67165 : checkPrefixCuts (2^48) 8807383041 10 Manual.Count131072.C067165.packed 64 cuts67165 = true := by
 decide +kernel
def cuts67166 : List PrefixCut := [⟨14,40778973,40778997⟩,
⟨64,183280616,183280725⟩]
theorem checked67166 : checkPrefixCuts (2^48) 8807514113 10 Manual.Count131072.C067166.packed 64 cuts67166 = true := by
 decide +kernel
def pointBounds67166 : List (Nat × Nat × Nat) := [(8807542784,115306472782020,115306861990111)]
theorem point_links_checked67166 : (cuts67166.take 1).map (fun c => (8807514113-1+2*2^10*c.k,115306432003047+c.lower,115306821211114+c.upper)) = pointBounds67166 := by
 decide +kernel
def cuts67167 : List PrefixCut := [⟨64,181584119,181584231⟩]
theorem checked67167 : checkPrefixCuts (2^48) 8807645185 10 Manual.Count131072.C067167.packed 64 cuts67167 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000223
