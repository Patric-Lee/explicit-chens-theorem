import PlattAssemblyKernel
import PlattCertificates.Count131072.C061152
import PlattCertificates.Count131072.C061153
import PlattCertificates.Count131072.C061154
import PlattCertificates.Count131072.C061155
import PlattCertificates.Count131072.C061156
import PlattCertificates.Count131072.C061157
import PlattCertificates.Count131072.C061158
import PlattCertificates.Count131072.C061159
import PlattCertificates.Count131072.C061160
import PlattCertificates.Count131072.C061161
import PlattCertificates.Count131072.C061162
import PlattCertificates.Count131072.C061163
import PlattCertificates.Count131072.C061164
import PlattCertificates.Count131072.C061165
import PlattCertificates.Count131072.C061166
import PlattCertificates.Count131072.C061167
import PlattCertificates.Count131072.C061168
import PlattCertificates.Count131072.C061169
import PlattCertificates.Count131072.C061170
import PlattCertificates.Count131072.C061171
import PlattCertificates.Count131072.C061172
import PlattCertificates.Count131072.C061173
import PlattCertificates.Count131072.C061174
import PlattCertificates.Count131072.C061175
import PlattCertificates.Count131072.C061176
import PlattCertificates.Count131072.C061177
import PlattCertificates.Count131072.C061178
import PlattCertificates.Count131072.C061179
import PlattCertificates.Count131072.C061180
import PlattCertificates.Count131072.C061181
import PlattCertificates.Count131072.C061182
import PlattCertificates.Count131072.C061183
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61152 : List PrefixCut := [⟨64,203858642,203858767⟩]
theorem checked61152 : checkPrefixCuts (2^48) 8019247105 10 Manual.Count131072.C061152.packed 64 cuts61152 = true := by
 decide +kernel
def cuts61153 : List PrefixCut := [⟨41,128743712,128743788⟩,
⟨64,199818924,199819040⟩]
theorem checked61153 : checkPrefixCuts (2^48) 8019378177 10 Manual.Count131072.C061153.packed 64 cuts61153 = true := by
 decide +kernel
def pointBounds61153 : List (Nat × Nat × Nat) := [(8019462144,114151882431105,114152270972718)]
theorem point_links_checked61153 : (cuts61153.take 1).map (fun c => (8019378177-1+2*2^10*c.k,114151753687393+c.lower,114152142228930+c.upper)) = pointBounds61153 := by
 decide +kernel
def cuts61154 : List PrefixCut := [⟨64,201149397,201149516⟩]
theorem checked61154 : checkPrefixCuts (2^48) 8019509249 10 Manual.Count131072.C061154.packed 64 cuts61154 = true := by
 decide +kernel
def cuts61155 : List PrefixCut := [⟨36,114559979,114560048⟩,
⟨64,205041972,205042093⟩]
theorem checked61155 : checkPrefixCuts (2^48) 8019640321 10 Manual.Count131072.C061155.packed 64 cuts61155 = true := by
 decide +kernel
def pointBounds61155 : List (Nat × Nat × Nat) := [(8019714048,114152269215693,114152657757534)]
theorem point_links_checked61155 : (cuts61155.take 1).map (fun c => (8019640321-1+2*2^10*c.k,114152154655714+c.lower,114152543197486+c.upper)) = pointBounds61155 := by
 decide +kernel
def cuts61156 : List PrefixCut := [⟨64,203213561,203213678⟩]
theorem checked61156 : checkPrefixCuts (2^48) 8019771393 10 Manual.Count131072.C061156.packed 64 cuts61156 = true := by
 decide +kernel
def cuts61157 : List PrefixCut := [⟨31,97288626,97288680⟩,
⟨64,201034242,201034356⟩]
theorem checked61157 : checkPrefixCuts (2^48) 8019902465 10 Manual.Count131072.C061157.packed 64 cuts61157 = true := by
 decide +kernel
def pointBounds61157 : List (Nat × Nat × Nat) := [(8019965952,114152660199873,114153048741937)]
theorem point_links_checked61157 : (cuts61157.take 1).map (fun c => (8019902465-1+2*2^10*c.k,114152562911247+c.lower,114152951453257+c.upper)) = pointBounds61157 := by
 decide +kernel
def cuts61158 : List PrefixCut := [⟨64,200329049,200329166⟩]
theorem checked61158 : checkPrefixCuts (2^48) 8020033537 10 Manual.Count131072.C061158.packed 64 cuts61158 = true := by
 decide +kernel
def cuts61159 : List PrefixCut := [⟨26,80790496,80790542⟩,
⟨64,200676709,200676827⟩]
theorem checked61159 : checkPrefixCuts (2^48) 8020164609 10 Manual.Count131072.C061159.packed 64 cuts61159 = true := by
 decide +kernel
def pointBounds61159 : List (Nat × Nat × Nat) := [(8020217856,114153045065034,114153433607321)]
theorem point_links_checked61159 : (cuts61159.take 1).map (fun c => (8020164609-1+2*2^10*c.k,114152964274538+c.lower,114153352816779+c.upper)) = pointBounds61159 := by
 decide +kernel
def cuts61160 : List PrefixCut := [⟨64,201164766,201164881⟩]
theorem checked61160 : checkPrefixCuts (2^48) 8020295681 10 Manual.Count131072.C061160.packed 64 cuts61160 = true := by
 decide +kernel
def cuts61161 : List PrefixCut := [⟨21,66364003,66364038⟩,
⟨64,201828278,201828387⟩]
theorem checked61161 : checkPrefixCuts (2^48) 8020426753 10 Manual.Count131072.C061161.packed 64 cuts61161 = true := by
 decide +kernel
def pointBounds61161 : List (Nat × Nat × Nat) := [(8020469760,114153432480016,114153821022525)]
theorem point_links_checked61161 : (cuts61161.take 1).map (fun c => (8020426753-1+2*2^10*c.k,114153366116013+c.lower,114153754658487+c.upper)) = pointBounds61161 := by
 decide +kernel
def cuts61162 : List PrefixCut := [⟨64,204211370,204211485⟩]
theorem checked61162 : checkPrefixCuts (2^48) 8020557825 10 Manual.Count131072.C061162.packed 64 cuts61162 = true := by
 decide +kernel
def cuts61163 : List PrefixCut := [⟨16,50885625,50885655⟩,
⟨64,202909565,202909683⟩]
theorem checked61163 : checkPrefixCuts (2^48) 8020688897 10 Manual.Count131072.C061163.packed 64 cuts61163 = true := by
 decide +kernel
def pointBounds61163 : List (Nat × Nat × Nat) := [(8020721664,114153823041286,114154211584014)]
theorem point_links_checked61163 : (cuts61163.take 1).map (fun c => (8020688897-1+2*2^10*c.k,114153772155661+c.lower,114154160698359+c.upper)) = pointBounds61163 := by
 decide +kernel
def cuts61164 : List PrefixCut := [⟨64,202309663,202309785⟩]
theorem checked61164 : checkPrefixCuts (2^48) 8020819969 10 Manual.Count131072.C061164.packed 64 cuts61164 = true := by
 decide +kernel
def cuts61165 : List PrefixCut := [⟨11,34355470,34355488⟩,
⟨64,201920351,201920468⟩]
theorem checked61165 : checkPrefixCuts (2^48) 8020951041 10 Manual.Count131072.C061165.packed 64 cuts61165 = true := by
 decide +kernel
def pointBounds61165 : List (Nat × Nat × Nat) := [(8020973568,114154211730359,114154600273315)]
theorem point_links_checked61165 : (cuts61165.take 1).map (fun c => (8020951041-1+2*2^10*c.k,114154177374889+c.lower,114154565917827+c.upper)) = pointBounds61165 := by
 decide +kernel
def cuts61166 : List PrefixCut := [⟨64,200829223,200829338⟩]
theorem checked61166 : checkPrefixCuts (2^48) 8021082113 10 Manual.Count131072.C061166.packed 64 cuts61166 = true := by
 decide +kernel
def cuts61167 : List PrefixCut := [⟨6,18914204,18914214⟩,
⟨64,202861222,202861338⟩]
theorem checked61167 : checkPrefixCuts (2^48) 8021213185 10 Manual.Count131072.C061167.packed 64 cuts61167 = true := by
 decide +kernel
def pointBounds61167 : List (Nat × Nat × Nat) := [(8021225472,114154599038667,114154987581847)]
theorem point_links_checked61167 : (cuts61167.take 1).map (fun c => (8021213185-1+2*2^10*c.k,114154580124463+c.lower,114154968667633+c.upper)) = pointBounds61167 := by
 decide +kernel
def cuts61168 : List PrefixCut := [⟨64,200822657,200822770⟩]
theorem checked61168 : checkPrefixCuts (2^48) 8021344257 10 Manual.Count131072.C061168.packed 64 cuts61168 = true := by
 decide +kernel
def cuts61169 : List PrefixCut := [⟨1,3509016,3509018⟩,
⟨64,202258060,202258173⟩]
theorem checked61169 : checkPrefixCuts (2^48) 8021475329 10 Manual.Count131072.C061169.packed 64 cuts61169 = true := by
 decide +kernel
def pointBounds61169 : List (Nat × Nat × Nat) := [(8021477376,114154987317358,114155375860759)]
theorem point_links_checked61169 : (cuts61169.take 1).map (fun c => (8021475329-1+2*2^10*c.k,114154983808342+c.lower,114155372351741+c.upper)) = pointBounds61169 := by
 decide +kernel
def cuts61170 : List PrefixCut := [⟨60,189833239,189833350⟩,
⟨64,202254757,202254875⟩]
theorem checked61170 : checkPrefixCuts (2^48) 8021606401 10 Manual.Count131072.C061170.packed 64 cuts61170 = true := by
 decide +kernel
def pointBounds61170 : List (Nat × Nat × Nat) := [(8021729280,114155375899641,114155764443264)]
theorem point_links_checked61170 : (cuts61170.take 1).map (fun c => (8021606401-1+2*2^10*c.k,114155186066402+c.lower,114155574609914+c.upper)) = pointBounds61170 := by
 decide +kernel
def cuts61171 : List PrefixCut := [⟨64,201339127,201339248⟩]
theorem checked61171 : checkPrefixCuts (2^48) 8021737473 10 Manual.Count131072.C061171.packed 64 cuts61171 = true := by
 decide +kernel
def cuts61172 : List PrefixCut := [⟨55,172107599,172107691⟩,
⟨64,200423545,200423654⟩]
theorem checked61172 : checkPrefixCuts (2^48) 8021868545 10 Manual.Count131072.C061172.packed 64 cuts61172 = true := by
 decide +kernel
def pointBounds61172 : List (Nat × Nat × Nat) := [(8021981184,114155761767885,114156150311728)]
theorem point_links_checked61172 : (cuts61172.take 1).map (fun c => (8021868545-1+2*2^10*c.k,114155589660286+c.lower,114155978204037+c.upper)) = pointBounds61172 := by
 decide +kernel
def cuts61173 : List PrefixCut := [⟨64,202911514,202911633⟩]
theorem checked61173 : checkPrefixCuts (2^48) 8021999617 10 Manual.Count131072.C061173.packed 64 cuts61173 = true := by
 decide +kernel
def cuts61174 : List PrefixCut := [⟨50,157856745,157856840⟩,
⟨64,202346793,202346914⟩]
theorem checked61174 : checkPrefixCuts (2^48) 8022130689 10 Manual.Count131072.C061174.packed 64 cuts61174 = true := by
 decide +kernel
def pointBounds61174 : List (Nat × Nat × Nat) := [(8022233088,114156150852090,114156539396164)]
theorem point_links_checked61174 : (cuts61174.take 1).map (fun c => (8022130689-1+2*2^10*c.k,114155992995345+c.lower,114156381539324+c.upper)) = pointBounds61174 := by
 decide +kernel
def cuts61175 : List PrefixCut := [⟨64,199536575,199536690⟩]
theorem checked61175 : checkPrefixCuts (2^48) 8022261761 10 Manual.Count131072.C061175.packed 64 cuts61175 = true := by
 decide +kernel
def cuts61176 : List PrefixCut := [⟨45,141501636,141501716⟩,
⟨64,200936749,200936866⟩]
theorem checked61176 : checkPrefixCuts (2^48) 8022392833 10 Manual.Count131072.C061176.packed 64 cuts61176 = true := by
 decide +kernel
def pointBounds61176 : List (Nat × Nat × Nat) := [(8022484992,114156536380349,114156924924644)]
theorem point_links_checked61176 : (cuts61176.take 1).map (fun c => (8022392833-1+2*2^10*c.k,114156394878713+c.lower,114156783422928+c.upper)) = pointBounds61176 := by
 decide +kernel
def cuts61177 : List PrefixCut := [⟨64,199284454,199284562⟩]
theorem checked61177 : checkPrefixCuts (2^48) 8022523905 10 Manual.Count131072.C061177.packed 64 cuts61177 = true := by
 decide +kernel
def cuts61178 : List PrefixCut := [⟨40,125533509,125533579⟩,
⟨64,200228497,200228607⟩]
theorem checked61178 : checkPrefixCuts (2^48) 8022654977 10 Manual.Count131072.C061178.packed 64 cuts61178 = true := by
 decide +kernel
def pointBounds61178 : List (Nat × Nat × Nat) := [(8022736896,114156920633425,114157309177935)]
theorem point_links_checked61178 : (cuts61178.take 1).map (fun c => (8022654977-1+2*2^10*c.k,114156795099916+c.lower,114157183644356+c.upper)) = pointBounds61178 := by
 decide +kernel
def cuts61179 : List PrefixCut := [⟨64,204926496,204926617⟩]
theorem checked61179 : checkPrefixCuts (2^48) 8022786049 10 Manual.Count131072.C061179.packed 64 cuts61179 = true := by
 decide +kernel
def cuts61180 : List PrefixCut := [⟨35,110092657,110092722⟩,
⟨64,202537460,202537579⟩]
theorem checked61180 : checkPrefixCuts (2^48) 8022917121 10 Manual.Count131072.C061180.packed 64 cuts61180 = true := by
 decide +kernel
def pointBounds61180 : List (Nat × Nat × Nat) := [(8022988800,114157310347566,114157698892302)]
theorem point_links_checked61180 : (cuts61180.take 1).map (fun c => (8022917121-1+2*2^10*c.k,114157200254909+c.lower,114157588799580+c.upper)) = pointBounds61180 := by
 decide +kernel
def cuts61181 : List PrefixCut := [⟨64,201236101,201236218⟩]
theorem checked61181 : checkPrefixCuts (2^48) 8023048193 10 Manual.Count131072.C061181.packed 64 cuts61181 = true := by
 decide +kernel
def cuts61182 : List PrefixCut := [⟨30,94758046,94758100⟩,
⟨64,200145254,200145368⟩]
theorem checked61182 : checkPrefixCuts (2^48) 8023179265 10 Manual.Count131072.C061182.packed 64 cuts61182 = true := by
 decide +kernel
def pointBounds61182 : List (Nat × Nat × Nat) := [(8023240704,114157698786516,114158087331477)]
theorem point_links_checked61182 : (cuts61182.take 1).map (fun c => (8023179265-1+2*2^10*c.k,114157604028470+c.lower,114157992573377+c.upper)) = pointBounds61182 := by
 decide +kernel
def cuts61183 : List PrefixCut := [⟨64,199826246,199826363⟩]
theorem checked61183 : checkPrefixCuts (2^48) 8023310337 10 Manual.Count131072.C061183.packed 64 cuts61183 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000036
