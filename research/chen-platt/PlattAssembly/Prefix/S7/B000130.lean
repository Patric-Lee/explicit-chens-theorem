import PlattAssemblyKernel
import PlattCertificates.Count131072.C064160
import PlattCertificates.Count131072.C064161
import PlattCertificates.Count131072.C064162
import PlattCertificates.Count131072.C064163
import PlattCertificates.Count131072.C064164
import PlattCertificates.Count131072.C064165
import PlattCertificates.Count131072.C064166
import PlattCertificates.Count131072.C064167
import PlattCertificates.Count131072.C064168
import PlattCertificates.Count131072.C064169
import PlattCertificates.Count131072.C064170
import PlattCertificates.Count131072.C064171
import PlattCertificates.Count131072.C064172
import PlattCertificates.Count131072.C064173
import PlattCertificates.Count131072.C064174
import PlattCertificates.Count131072.C064175
import PlattCertificates.Count131072.C064176
import PlattCertificates.Count131072.C064177
import PlattCertificates.Count131072.C064178
import PlattCertificates.Count131072.C064179
import PlattCertificates.Count131072.C064180
import PlattCertificates.Count131072.C064181
import PlattCertificates.Count131072.C064182
import PlattCertificates.Count131072.C064183
import PlattCertificates.Count131072.C064184
import PlattCertificates.Count131072.C064185
import PlattCertificates.Count131072.C064186
import PlattCertificates.Count131072.C064187
import PlattCertificates.Count131072.C064188
import PlattCertificates.Count131072.C064189
import PlattCertificates.Count131072.C064190
import PlattCertificates.Count131072.C064191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64160 : List PrefixCut := [⟨14,41183159,41183185⟩,
⟨64,191528952,191529068⟩]
theorem checked64160 : checkPrefixCuts (2^48) 8413511681 10 Manual.Count131072.C064160.packed 64 cuts64160 = true := by
 decide +kernel
def pointBounds64160 : List (Nat × Nat × Nat) := [(8413540352,114743371104261,114743759985843)]
theorem point_links_checked64160 : (cuts64160.take 1).map (fun c => (8413511681-1+2*2^10*c.k,114743329921102+c.lower,114743718802658+c.upper)) = pointBounds64160 := by
 decide +kernel
def cuts64161 : List PrefixCut := [⟨64,192897598,192897713⟩]
theorem checked64161 : checkPrefixCuts (2^48) 8413642753 10 Manual.Count131072.C064161.packed 64 cuts64161 = true := by
 decide +kernel
def cuts64162 : List PrefixCut := [⟨15,44962174,44962201⟩,
⟨64,192091715,192091829⟩]
theorem checked64162 : checkPrefixCuts (2^48) 8413773825 10 Manual.Count131072.C064162.packed 64 cuts64162 = true := by
 decide +kernel
def pointBounds64162 : List (Nat × Nat × Nat) := [(8413804544,114743759309826,114744148191640)]
theorem point_links_checked64162 : (cuts64162.take 1).map (fun c => (8413773825-1+2*2^10*c.k,114743714347652+c.lower,114744103229439+c.upper)) = pointBounds64162 := by
 decide +kernel
def cuts64163 : List PrefixCut := [⟨64,191252381,191252498⟩]
theorem checked64163 : checkPrefixCuts (2^48) 8413904897 10 Manual.Count131072.C064163.packed 64 cuts64163 = true := by
 decide +kernel
def cuts64164 : List PrefixCut := [⟨16,49811447,49811474⟩,
⟨64,194393975,194394084⟩]
theorem checked64164 : checkPrefixCuts (2^48) 8414035969 10 Manual.Count131072.C064164.packed 64 cuts64164 = true := by
 decide +kernel
def pointBounds64164 : List (Nat × Nat × Nat) := [(8414068736,114744147503195,114744536385240)]
theorem point_links_checked64164 : (cuts64164.take 1).map (fun c => (8414035969-1+2*2^10*c.k,114744097691748+c.lower,114744486573766+c.upper)) = pointBounds64164 := by
 decide +kernel
def cuts64165 : List PrefixCut := [⟨64,196766045,196766160⟩]
theorem checked64165 : checkPrefixCuts (2^48) 8414167041 10 Manual.Count131072.C064165.packed 64 cuts64165 = true := by
 decide +kernel
def cuts64166 : List PrefixCut := [⟨17,49073949,49073975⟩,
⟨64,193417804,193417908⟩]
theorem checked64166 : checkPrefixCuts (2^48) 8414298113 10 Manual.Count131072.C064166.packed 64 cuts64166 = true := by
 decide +kernel
def pointBounds64166 : List (Nat × Nat × Nat) := [(8414332928,114744537925717,114744926807985)]
theorem point_links_checked64166 : (cuts64166.take 1).map (fun c => (8414298113-1+2*2^10*c.k,114744488851768+c.lower,114744877734010+c.upper)) = pointBounds64166 := by
 decide +kernel
def cuts64167 : List PrefixCut := [⟨64,187928806,187928916⟩]
theorem checked64167 : checkPrefixCuts (2^48) 8414429185 10 Manual.Count131072.C064167.packed 64 cuts64167 = true := by
 decide +kernel
def cuts64168 : List PrefixCut := [⟨18,52350595,52350625⟩,
⟨64,192207557,192207659⟩]
theorem checked64168 : checkPrefixCuts (2^48) 8414560257 10 Manual.Count131072.C064168.packed 64 cuts64168 = true := by
 decide +kernel
def pointBounds64168 : List (Nat × Nat × Nat) := [(8414597120,114744922548973,114745311431459)]
theorem point_links_checked64168 : (cuts64168.take 1).map (fun c => (8414560257-1+2*2^10*c.k,114744870198378+c.lower,114745259080834+c.upper)) = pointBounds64168 := by
 decide +kernel
def cuts64169 : List PrefixCut := [⟨64,191736284,191736388⟩]
theorem checked64169 : checkPrefixCuts (2^48) 8414691329 10 Manual.Count131072.C064169.packed 64 cuts64169 = true := by
 decide +kernel
def cuts64170 : List PrefixCut := [⟨19,55493242,55493272⟩,
⟨64,192034330,192034441⟩]
theorem checked64170 : checkPrefixCuts (2^48) 8414822401 10 Manual.Count131072.C064170.packed 64 cuts64170 = true := by
 decide +kernel
def pointBounds64170 : List (Nat × Nat × Nat) := [(8414861312,114745309635461,114745698518153)]
theorem point_links_checked64170 : (cuts64170.take 1).map (fun c => (8414822401-1+2*2^10*c.k,114745254142219+c.lower,114745643024881+c.upper)) = pointBounds64170 := by
 decide +kernel
def cuts64171 : List PrefixCut := [⟨64,192633420,192633535⟩]
theorem checked64171 : checkPrefixCuts (2^48) 8414953473 10 Manual.Count131072.C064171.packed 64 cuts64171 = true := by
 decide +kernel
def cuts64172 : List PrefixCut := [⟨20,59572254,59572292⟩,
⟨64,192530072,192530192⟩]
theorem checked64172 : checkPrefixCuts (2^48) 8415084545 10 Manual.Count131072.C064172.packed 64 cuts64172 = true := by
 decide +kernel
def pointBounds64172 : List (Nat × Nat × Nat) := [(8415125504,114745698382223,114746087265149)]
theorem point_links_checked64172 : (cuts64172.take 1).map (fun c => (8415084545-1+2*2^10*c.k,114745638809969+c.lower,114746027692857+c.upper)) = pointBounds64172 := by
 decide +kernel
def cuts64173 : List PrefixCut := [⟨64,191690880,191690994⟩]
theorem checked64173 : checkPrefixCuts (2^48) 8415215617 10 Manual.Count131072.C064173.packed 64 cuts64173 = true := by
 decide +kernel
def cuts64174 : List PrefixCut := [⟨21,62714481,62714516⟩,
⟨64,189580702,189580814⟩]
theorem checked64174 : checkPrefixCuts (2^48) 8415346689 10 Manual.Count131072.C064174.packed 64 cuts64174 = true := by
 decide +kernel
def pointBounds64174 : List (Nat × Nat × Nat) := [(8415389696,114746085745402,114746474628559)]
theorem point_links_checked64174 : (cuts64174.take 1).map (fun c => (8415346689-1+2*2^10*c.k,114746023030921+c.lower,114746411914043+c.upper)) = pointBounds64174 := by
 decide +kernel
def cuts64175 : List PrefixCut := [⟨64,192755204,192755320⟩]
theorem checked64175 : checkPrefixCuts (2^48) 8415477761 10 Manual.Count131072.C064175.packed 64 cuts64175 = true := by
 decide +kernel
def cuts64176 : List PrefixCut := [⟨22,65588932,65588971⟩,
⟨64,191314010,191314118⟩]
theorem checked64176 : checkPrefixCuts (2^48) 8415608833 10 Manual.Count131072.C064176.packed 64 cuts64176 = true := by
 decide +kernel
def pointBounds64176 : List (Nat × Nat × Nat) := [(8415653888,114746470955759,114746859839148)]
theorem point_links_checked64176 : (cuts64176.take 1).map (fun c => (8415608833-1+2*2^10*c.k,114746405366827+c.lower,114746794250177+c.upper)) = pointBounds64176 := by
 decide +kernel
def cuts64177 : List PrefixCut := [⟨64,191076904,191077010⟩]
theorem checked64177 : checkPrefixCuts (2^48) 8415739905 10 Manual.Count131072.C064177.packed 64 cuts64177 = true := by
 decide +kernel
def cuts64178 : List PrefixCut := [⟨23,68697326,68697367⟩,
⟨64,190271239,190271352⟩]
theorem checked64178 : checkPrefixCuts (2^48) 8415870977 10 Manual.Count131072.C064178.packed 64 cuts64178 = true := by
 decide +kernel
def pointBounds64178 : List (Nat × Nat × Nat) := [(8415918080,114746856455067,114747245338672)]
theorem point_links_checked64178 : (cuts64178.take 1).map (fun c => (8415870977-1+2*2^10*c.k,114746787757741+c.lower,114747176641305+c.upper)) = pointBounds64178 := by
 decide +kernel
def cuts64179 : List PrefixCut := [⟨64,191572632,191572747⟩]
theorem checked64179 : checkPrefixCuts (2^48) 8416002049 10 Manual.Count131072.C064179.packed 64 cuts64179 = true := by
 decide +kernel
def cuts64180 : List PrefixCut := [⟨24,72641641,72641682⟩,
⟨64,192171651,192171764⟩]
theorem checked64180 : checkPrefixCuts (2^48) 8416133121 10 Manual.Count131072.C064180.packed 64 cuts64180 = true := by
 decide +kernel
def pointBounds64180 : List (Nat × Nat × Nat) := [(8416182272,114747242243253,114747631127086)]
theorem point_links_checked64180 : (cuts64180.take 1).map (fun c => (8416133121-1+2*2^10*c.k,114747169601612+c.lower,114747558485404+c.upper)) = pointBounds64180 := by
 decide +kernel
def cuts64181 : List PrefixCut := [⟨64,191600120,191600226⟩]
theorem checked64181 : checkPrefixCuts (2^48) 8416264193 10 Manual.Count131072.C064181.packed 64 cuts64181 = true := by
 decide +kernel
def cuts64182 : List PrefixCut := [⟨25,74244656,74244700⟩,
⟨64,191496801,191496909⟩]
theorem checked64182 : checkPrefixCuts (2^48) 8416395265 10 Manual.Count131072.C064182.packed 64 cuts64182 = true := by
 decide +kernel
def pointBounds64182 : List (Nat × Nat × Nat) := [(8416446464,114747627618039,114748016502094)]
theorem point_links_checked64182 : (cuts64182.take 1).map (fun c => (8416395265-1+2*2^10*c.k,114747553373383+c.lower,114747942257394+c.upper)) = pointBounds64182 := by
 decide +kernel
def cuts64183 : List PrefixCut := [⟨64,193734487,193734600⟩]
theorem checked64183 : checkPrefixCuts (2^48) 8416526337 10 Manual.Count131072.C064183.packed 64 cuts64183 = true := by
 decide +kernel
def cuts64184 : List PrefixCut := [⟨26,77385925,77385971⟩,
⟨64,191156404,191156509⟩]
theorem checked64184 : checkPrefixCuts (2^48) 8416657409 10 Manual.Count131072.C064184.packed 64 cuts64184 = true := by
 decide +kernel
def pointBounds64184 : List (Nat × Nat × Nat) := [(8416710656,114748015990596,114748404874874)]
theorem point_links_checked64184 : (cuts64184.take 1).map (fun c => (8416657409-1+2*2^10*c.k,114747938604671+c.lower,114748327488903+c.upper)) = pointBounds64184 := by
 decide +kernel
def cuts64185 : List PrefixCut := [⟨64,196403793,196403900⟩]
theorem checked64185 : checkPrefixCuts (2^48) 8416788481 10 Manual.Count131072.C064185.packed 64 cuts64185 = true := by
 decide +kernel
def cuts64186 : List PrefixCut := [⟨27,80527005,80527052⟩,
⟨64,190113771,190113880⟩]
theorem checked64186 : checkPrefixCuts (2^48) 8416919553 10 Manual.Count131072.C064186.packed 64 cuts64186 = true := by
 decide +kernel
def pointBounds64186 : List (Nat × Nat × Nat) := [(8416974848,114748406691873,114748795576364)]
theorem point_links_checked64186 : (cuts64186.take 1).map (fun c => (8416919553-1+2*2^10*c.k,114748326164868+c.lower,114748715049312+c.upper)) = pointBounds64186 := by
 decide +kernel
def cuts64187 : List PrefixCut := [⟨64,192585437,192585551⟩]
theorem checked64187 : checkPrefixCuts (2^48) 8417050625 10 Manual.Count131072.C064187.packed 64 cuts64187 = true := by
 decide +kernel
def cuts64188 : List PrefixCut := [⟨28,83567564,83567614⟩,
⟨64,193084027,193084141⟩]
theorem checked64188 : checkPrefixCuts (2^48) 8417181697 10 Manual.Count131072.C064188.packed 64 cuts64188 = true := by
 decide +kernel
def pointBounds64188 : List (Nat × Nat × Nat) := [(8417239040,114748792431640,114749181316357)]
theorem point_links_checked64188 : (cuts64188.take 1).map (fun c => (8417181697-1+2*2^10*c.k,114748708864076+c.lower,114749097748743+c.upper)) = pointBounds64188 := by
 decide +kernel
def cuts64189 : List PrefixCut := [⟨64,187830986,187831097⟩]
theorem checked64189 : checkPrefixCuts (2^48) 8417312769 10 Manual.Count131072.C064189.packed 64 cuts64189 = true := by
 decide +kernel
def cuts64190 : List PrefixCut := [⟨29,87845194,87845240⟩,
⟨64,193312105,193312213⟩]
theorem checked64190 : checkPrefixCuts (2^48) 8417443841 10 Manual.Count131072.C064190.packed 64 cuts64190 = true := by
 decide +kernel
def pointBounds64190 : List (Nat × Nat × Nat) := [(8417503232,114749177624283,114749566509221)]
theorem point_links_checked64190 : (cuts64190.take 1).map (fun c => (8417443841-1+2*2^10*c.k,114749089779089+c.lower,114749478663981+c.upper)) = pointBounds64190 := by
 decide +kernel
def cuts64191 : List PrefixCut := [⟨64,190734295,190734403⟩]
theorem checked64191 : checkPrefixCuts (2^48) 8417574913 10 Manual.Count131072.C064191.packed 64 cuts64191 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000130
