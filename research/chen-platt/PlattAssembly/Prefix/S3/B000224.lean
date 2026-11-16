import PlattAssemblyKernel
import PlattCertificates.Count131072.C027168
import PlattCertificates.Count131072.C027169
import PlattCertificates.Count131072.C027170
import PlattCertificates.Count131072.C027171
import PlattCertificates.Count131072.C027172
import PlattCertificates.Count131072.C027173
import PlattCertificates.Count131072.C027174
import PlattCertificates.Count131072.C027175
import PlattCertificates.Count131072.C027176
import PlattCertificates.Count131072.C027177
import PlattCertificates.Count131072.C027178
import PlattCertificates.Count131072.C027179
import PlattCertificates.Count131072.C027180
import PlattCertificates.Count131072.C027181
import PlattCertificates.Count131072.C027182
import PlattCertificates.Count131072.C027183
import PlattCertificates.Count131072.C027184
import PlattCertificates.Count131072.C027185
import PlattCertificates.Count131072.C027186
import PlattCertificates.Count131072.C027187
import PlattCertificates.Count131072.C027188
import PlattCertificates.Count131072.C027189
import PlattCertificates.Count131072.C027190
import PlattCertificates.Count131072.C027191
import PlattCertificates.Count131072.C027192
import PlattCertificates.Count131072.C027193
import PlattCertificates.Count131072.C027194
import PlattCertificates.Count131072.C027195
import PlattCertificates.Count131072.C027196
import PlattCertificates.Count131072.C027197
import PlattCertificates.Count131072.C027198
import PlattCertificates.Count131072.C027199
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000224
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27168 : List PrefixCut := [⟨12,41847344,41847368⟩,
⟨121,446259382,446259633⟩,
⟨128,472235433,472235700⟩]
theorem checked27168 : checkPrefixCuts (2^48) 3564896257 9 Manual.Count131072.C027168.packed 128 cuts27168 = true := by
 decide +kernel
def pointBounds27168 : List (Nat × Nat × Nat) := [(3564908544,103963219147494,103963601760401),(3565020160,103963623559532,103964006172666)]
theorem point_links_checked27168 : (cuts27168.take 2).map (fun c => (3564896257-1+2*2^9*c.k,103963177300150+c.lower,103963559913033+c.upper)) = pointBounds27168 := by
 decide +kernel
def cuts27169 : List PrefixCut := [⟨102,376054667,376054877⟩,
⟨128,471033773,471034036⟩]
theorem checked27169 : checkPrefixCuts (2^48) 3565027329 9 Manual.Count131072.C027169.packed 128 cuts27169 = true := by
 decide +kernel
def pointBounds27169 : List (Nat × Nat × Nat) := [(3565131776,103964025590250,103964408203610)]
theorem point_links_checked27169 : (cuts27169.take 1).map (fun c => (3565027329-1+2*2^9*c.k,103963649535583+c.lower,103964032148733+c.upper)) = pointBounds27169 := by
 decide +kernel
def cuts27170 : List PrefixCut := [⟨83,303012523,303012694⟩,
⟨128,469358473,469358739⟩]
theorem checked27170 : checkPrefixCuts (2^48) 3565158401 9 Manual.Count131072.C027170.packed 128 cuts27170 = true := by
 decide +kernel
def pointBounds27170 : List (Nat × Nat × Nat) := [(3565243392,103964423581879,103964806195463)]
theorem point_links_checked27170 : (cuts27170.take 1).map (fun c => (3565158401-1+2*2^9*c.k,103964120569356+c.lower,103964503182769+c.upper)) = pointBounds27170 := by
 decide +kernel
def cuts27171 : List PrefixCut := [⟨64,231712245,231712374⟩,
⟨128,464999139,464999398⟩]
theorem checked27171 : checkPrefixCuts (2^48) 3565289473 9 Manual.Count131072.C027171.packed 128 cuts27171 = true := by
 decide +kernel
def pointBounds27171 : List (Nat × Nat × Nat) := [(3565355008,103964821640074,103965204253882)]
theorem point_links_checked27171 : (cuts27171.take 1).map (fun c => (3565289473-1+2*2^9*c.k,103964589927829+c.lower,103964972541508+c.upper)) = pointBounds27171 := by
 decide +kernel
def cuts27172 : List PrefixCut := [⟨45,163969315,163969408⟩,
⟨128,475718443,475718708⟩]
theorem checked27172 : checkPrefixCuts (2^48) 3565420545 9 Manual.Count131072.C027172.packed 128 cuts27172 = true := by
 decide +kernel
def pointBounds27172 : List (Nat × Nat × Nat) := [(3565466624,103965218896283,103965601510314)]
theorem point_links_checked27172 : (cuts27172.take 1).map (fun c => (3565420545-1+2*2^9*c.k,103965054926968+c.lower,103965437540906+c.upper)) = pointBounds27172 := by
 decide +kernel
def cuts27173 : List PrefixCut := [⟨26,95204747,95204803⟩,
⟨128,467491071,467491341⟩]
theorem checked27173 : checkPrefixCuts (2^48) 3565551617 9 Manual.Count131072.C027173.packed 128 cuts27173 = true := by
 decide +kernel
def pointBounds27173 : List (Nat × Nat × Nat) := [(3565578240,103965625850158,103966008464417)]
theorem point_links_checked27173 : (cuts27173.take 1).map (fun c => (3565551617-1+2*2^9*c.k,103965530645411+c.lower,103965913259614+c.upper)) = pointBounds27173 := by
 decide +kernel
def cuts27174 : List PrefixCut := [⟨7,26050166,26050179⟩,
⟨116,423821656,423821891⟩,
⟨128,468421179,468421437⟩]
theorem checked27174 : checkPrefixCuts (2^48) 3565682689 9 Manual.Count131072.C027174.packed 128 cuts27174 = true := by
 decide +kernel
def pointBounds27174 : List (Nat × Nat × Nat) := [(3565689856,103966024186648,103966406801134),(3565801472,103966421958138,103966804572846)]
theorem point_links_checked27174 : (cuts27174.take 2).map (fun c => (3565682689-1+2*2^9*c.k,103965998136482+c.lower,103966380750955+c.upper)) = pointBounds27174 := by
 decide +kernel
def cuts27175 : List PrefixCut := [⟨97,359948040,359948244⟩,
⟨128,473140142,473140408⟩]
theorem checked27175 : checkPrefixCuts (2^48) 3565813761 9 Manual.Count131072.C027175.packed 128 cuts27175 = true := by
 decide +kernel
def pointBounds27175 : List (Nat × Nat × Nat) := [(3565913088,103966826505701,103967209120636)]
theorem point_links_checked27175 : (cuts27175.take 1).map (fun c => (3565813761-1+2*2^9*c.k,103966466557661+c.lower,103966849172392+c.upper)) = pointBounds27175 := by
 decide +kernel
def cuts27176 : List PrefixCut := [⟨78,285185960,285186121⟩,
⟨128,467913177,467913439⟩]
theorem checked27176 : checkPrefixCuts (2^48) 3565944833 9 Manual.Count131072.C027176.packed 128 cuts27176 = true := by
 decide +kernel
def pointBounds27176 : List (Nat × Nat × Nat) := [(3566024704,103967224883763,103967607498921)]
theorem point_links_checked27176 : (cuts27176.take 1).map (fun c => (3565944833-1+2*2^9*c.k,103966939697803+c.lower,103967322312800+c.upper)) = pointBounds27176 := by
 decide +kernel
def cuts27177 : List PrefixCut := [⟨59,218637769,218637891⟩,
⟨128,472947480,472947746⟩]
theorem checked27177 : checkPrefixCuts (2^48) 3566075905 9 Manual.Count131072.C027177.packed 128 cuts27177 = true := by
 decide +kernel
def pointBounds27177 : List (Nat × Nat × Nat) := [(3566136320,103967626248749,103968008864130)]
theorem point_links_checked27177 : (cuts27177.take 1).map (fun c => (3566075905-1+2*2^9*c.k,103967407610980+c.lower,103967790226239+c.upper)) = pointBounds27177 := by
 decide +kernel
def cuts27178 : List PrefixCut := [⟨40,144280229,144280310⟩,
⟨128,470167593,470167859⟩]
theorem checked27178 : checkPrefixCuts (2^48) 3566206977 9 Manual.Count131072.C027178.packed 128 cuts27178 = true := by
 decide +kernel
def pointBounds27178 : List (Nat × Nat × Nat) := [(3566247936,103968024838689,103968407454295)]
theorem point_links_checked27178 : (cuts27178.take 1).map (fun c => (3566206977-1+2*2^9*c.k,103967880558460+c.lower,103968263173985+c.upper)) = pointBounds27178 := by
 decide +kernel
def cuts27179 : List PrefixCut := [⟨21,76636392,76636436⟩,
⟨128,470466078,470466342⟩]
theorem checked27179 : checkPrefixCuts (2^48) 3566338049 9 Manual.Count131072.C027179.packed 128 cuts27179 = true := by
 decide +kernel
def pointBounds27179 : List (Nat × Nat × Nat) := [(3566359552,103968427362445,103968809978280)]
theorem point_links_checked27179 : (cuts27179.take 1).map (fun c => (3566338049-1+2*2^9*c.k,103968350726053+c.lower,103968733341844+c.upper)) = pointBounds27179 := by
 decide +kernel
def cuts27180 : List PrefixCut := [⟨2,7734409,7734413⟩,
⟨111,409917243,409917476⟩,
⟨128,472816372,472816640⟩]
theorem checked27180 : checkPrefixCuts (2^48) 3566469121 9 Manual.Count131072.C027180.packed 128 cuts27180 = true := by
 decide +kernel
def pointBounds27180 : List (Nat × Nat × Nat) := [(3566471168,103968828926540,103969211542599),(3566582784,103969231109374,103969613725662)]
theorem point_links_checked27180 : (cuts27180.take 2).map (fun c => (3566469121-1+2*2^9*c.k,103968821192131+c.lower,103969203808186+c.upper)) = pointBounds27180 := by
 decide +kernel
def cuts27181 : List PrefixCut := [⟨92,336351236,336351425⟩,
⟨128,466880234,466880497⟩]
theorem checked27181 : checkPrefixCuts (2^48) 3566600193 9 Manual.Count131072.C027181.packed 128 cuts27181 = true := by
 decide +kernel
def pointBounds27181 : List (Nat × Nat × Nat) := [(3566694400,103969630359739,103970012976251)]
theorem point_links_checked27181 : (cuts27181.take 1).map (fun c => (3566600193-1+2*2^9*c.k,103969294008503+c.lower,103969676624826+c.upper)) = pointBounds27181 := by
 decide +kernel
def cuts27182 : List PrefixCut := [⟨73,264920826,264920977⟩,
⟨128,466073869,466074130⟩]
theorem checked27182 : checkPrefixCuts (2^48) 3566731265 9 Manual.Count131072.C027182.packed 128 cuts27182 = true := by
 decide +kernel
def pointBounds27182 : List (Nat × Nat × Nat) := [(3566806016,103970025809563,103970408426300)]
theorem point_links_checked27182 : (cuts27182.take 1).map (fun c => (3566731265-1+2*2^9*c.k,103969760888737+c.lower,103970143505323+c.upper)) = pointBounds27182 := by
 decide +kernel
def cuts27183 : List PrefixCut := [⟨54,201623377,201623490⟩,
⟨128,471107185,471107453⟩]
theorem checked27183 : checkPrefixCuts (2^48) 3566862337 9 Manual.Count131072.C027183.packed 128 cuts27183 = true := by
 decide +kernel
def pointBounds27183 : List (Nat × Nat × Nat) := [(3566917632,103970428585983,103970811202943)]
theorem point_links_checked27183 : (cuts27183.take 1).map (fun c => (3566862337-1+2*2^9*c.k,103970226962606+c.lower,103970609579453+c.upper)) = pointBounds27183 := by
 decide +kernel
def cuts27184 : List PrefixCut := [⟨35,130912652,130912726⟩,
⟨128,472352358,472352621⟩]
theorem checked27184 : checkPrefixCuts (2^48) 3566993409 9 Manual.Count131072.C027184.packed 128 cuts27184 = true := by
 decide +kernel
def pointBounds27184 : List (Nat × Nat × Nat) := [(3567029248,103970828982443,103971211599632)]
theorem point_links_checked27184 : (cuts27184.take 1).map (fun c => (3566993409-1+2*2^9*c.k,103970698069791+c.lower,103971080686906+c.upper)) = pointBounds27184 := by
 decide +kernel
def cuts27185 : List PrefixCut := [⟨16,58549647,58549681⟩,
⟨125,459078926,459079180⟩,
⟨128,470599086,470599346⟩]
theorem checked27185 : checkPrefixCuts (2^48) 3567124481 9 Manual.Count131072.C027185.packed 128 cuts27185 = true := by
 decide +kernel
def pointBounds27185 : List (Nat × Nat × Nat) := [(3567140864,103971228971796,103971611589208),(3567252480,103971629501075,103972012118707)]
theorem point_links_checked27185 : (cuts27185.take 2).map (fun c => (3567124481-1+2*2^9*c.k,103971170422149+c.lower,103971553039527+c.upper)) = pointBounds27185 := by
 decide +kernel
def cuts27186 : List PrefixCut := [⟨106,385051391,385051610⟩,
⟨128,462454760,462455022⟩]
theorem checked27186 : checkPrefixCuts (2^48) 3567255553 9 Manual.Count131072.C027186.packed 128 cuts27186 = true := by
 decide +kernel
def pointBounds27186 : List (Nat × Nat × Nat) := [(3567364096,103972026072626,103972408690483)]
theorem point_links_checked27186 : (cuts27186.take 1).map (fun c => (3567255553-1+2*2^9*c.k,103971641021235+c.lower,103972023638873+c.upper)) = pointBounds27186 := by
 decide +kernel
def cuts27187 : List PrefixCut := [⟨87,326098932,326099107⟩,
⟨128,472063641,472063898⟩]
theorem checked27187 : checkPrefixCuts (2^48) 3567386625 9 Manual.Count131072.C027187.packed 128 cuts27187 = true := by
 decide +kernel
def pointBounds27187 : List (Nat × Nat × Nat) := [(3567475712,103972429574927,103972812193002)]
theorem point_links_checked27187 : (cuts27187.take 1).map (fun c => (3567386625-1+2*2^9*c.k,103972103475995+c.lower,103972486093895+c.upper)) = pointBounds27187 := by
 decide +kernel
def cuts27188 : List PrefixCut := [⟨68,249556242,249556381⟩,
⟨128,470783846,470784110⟩]
theorem checked27188 : checkPrefixCuts (2^48) 3567517697 9 Manual.Count131072.C027188.packed 128 cuts27188 = true := by
 decide +kernel
def pointBounds27188 : List (Nat × Nat × Nat) := [(3567587328,103972825095878,103973207714174)]
theorem point_links_checked27188 : (cuts27188.take 1).map (fun c => (3567517697-1+2*2^9*c.k,103972575539636+c.lower,103972958157793+c.upper)) = pointBounds27188 := by
 decide +kernel
def cuts27189 : List PrefixCut := [⟨49,181302806,181302909⟩,
⟨128,474869102,474869370⟩]
theorem checked27189 : checkPrefixCuts (2^48) 3567648769 9 Manual.Count131072.C027189.packed 128 cuts27189 = true := by
 decide +kernel
def pointBounds27189 : List (Nat × Nat × Nat) := [(3567698944,103973227626288,103973610244812)]
theorem point_links_checked27189 : (cuts27189.take 1).map (fun c => (3567648769-1+2*2^9*c.k,103973046323482+c.lower,103973428941903+c.upper)) = pointBounds27189 := by
 decide +kernel
def cuts27190 : List PrefixCut := [⟨30,109740485,109740544⟩,
⟨128,470907069,470907327⟩]
theorem checked27190 : checkPrefixCuts (2^48) 3567779841 9 Manual.Count131072.C027190.packed 128 cuts27190 = true := by
 decide +kernel
def pointBounds27190 : List (Nat × Nat × Nat) := [(3567810560,103973630933069,103974013551817)]
theorem point_links_checked27190 : (cuts27190.take 1).map (fun c => (3567779841-1+2*2^9*c.k,103973521192584+c.lower,103973903811273+c.upper)) = pointBounds27190 := by
 decide +kernel
def cuts27191 : List PrefixCut := [⟨11,41338649,41338673⟩,
⟨120,446908054,446908300⟩,
⟨128,475544348,475544611⟩]
theorem checked27191 : checkPrefixCuts (2^48) 3567910913 9 Manual.Count131072.C027191.packed 128 cuts27191 = true := by
 decide +kernel
def pointBounds27191 : List (Nat × Nat × Nat) := [(3567922176,103974033438302,103974416057273),(3568033792,103974439007707,103974821626900)]
theorem point_links_checked27191 : (cuts27191.take 2).map (fun c => (3567910913-1+2*2^9*c.k,103973992099653+c.lower,103974374718600+c.upper)) = pointBounds27191 := by
 decide +kernel
def cuts27192 : List PrefixCut := [⟨101,369347265,369347473⟩,
⟨128,468742590,468742853⟩]
theorem checked27192 : checkPrefixCuts (2^48) 3568041985 9 Manual.Count131072.C027192.packed 128 cuts27192 = true := by
 decide +kernel
def pointBounds27192 : List (Nat × Nat × Nat) := [(3568145408,103974836991266,103975219610684)]
theorem point_links_checked27192 : (cuts27192.take 1).map (fun c => (3568041985-1+2*2^9*c.k,103974467644001+c.lower,103974850263211+c.upper)) = pointBounds27192 := by
 decide +kernel
def cuts27193 : List PrefixCut := [⟨82,300784510,300784678⟩,
⟨128,465254522,465254782⟩]
theorem checked27193 : checkPrefixCuts (2^48) 3568173057 9 Manual.Count131072.C027193.packed 128 cuts27193 = true := by
 decide +kernel
def pointBounds27193 : List (Nat × Nat × Nat) := [(3568257024,103975237171101,103975619790742)]
theorem point_links_checked27193 : (cuts27193.take 1).map (fun c => (3568173057-1+2*2^9*c.k,103974936386591+c.lower,103975319006064+c.upper)) = pointBounds27193 := by
 decide +kernel
def cuts27194 : List PrefixCut := [⟨63,235302806,235302935⟩,
⟨128,471311235,471311499⟩]
theorem checked27194 : checkPrefixCuts (2^48) 3568304129 9 Manual.Count131072.C027194.packed 128 cuts27194 = true := by
 decide +kernel
def pointBounds27194 : List (Nat × Nat × Nat) := [(3568368640,103975636943919,103976019563781)]
theorem point_links_checked27194 : (cuts27194.take 1).map (fun c => (3568304129-1+2*2^9*c.k,103975401641113+c.lower,103975784260846+c.upper)) = pointBounds27194 := by
 decide +kernel
def cuts27195 : List PrefixCut := [⟨44,163357547,163357636⟩,
⟨128,467902182,467902445⟩]
theorem checked27195 : checkPrefixCuts (2^48) 3568435201 9 Manual.Count131072.C027195.packed 128 cuts27195 = true := by
 decide +kernel
def pointBounds27195 : List (Nat × Nat × Nat) := [(3568480256,103976036309895,103976418929981)]
theorem point_links_checked27195 : (cuts27195.take 1).map (fun c => (3568435201-1+2*2^9*c.k,103975872952348+c.lower,103976255572345+c.upper)) = pointBounds27195 := by
 decide +kernel
def cuts27196 : List PrefixCut := [⟨25,95755344,95755396⟩,
⟨128,474510524,474510790⟩]
theorem checked27196 : checkPrefixCuts (2^48) 3568566273 9 Manual.Count131072.C027196.packed 128 cuts27196 = true := by
 decide +kernel
def pointBounds27196 : List (Nat × Nat × Nat) := [(3568591872,103976436609874,103976819230186)]
theorem point_links_checked27196 : (cuts27196.take 1).map (fun c => (3568566273-1+2*2^9*c.k,103976340854530+c.lower,103976723474790+c.upper)) = pointBounds27196 := by
 decide +kernel
def cuts27197 : List PrefixCut := [⟨6,21532389,21532401⟩,
⟨115,421886287,421886526⟩,
⟨128,470076183,470076448⟩]
theorem checked27197 : checkPrefixCuts (2^48) 3568697345 9 Manual.Count131072.C027197.packed 128 cuts27197 = true := by
 decide +kernel
def pointBounds27197 : List (Nat × Nat × Nat) := [(3568703488,103976836897443,103977219517981),(3568815104,103977237251341,103977619872106)]
theorem point_links_checked27197 : (cuts27197.take 2).map (fun c => (3568697345-1+2*2^9*c.k,103976815365054+c.lower,103977197985580+c.upper)) = pointBounds27197 := by
 decide +kernel
def cuts27198 : List PrefixCut := [⟨96,353492192,353492386⟩,
⟨128,469585679,469585939⟩]
theorem checked27198 : checkPrefixCuts (2^48) 3568828417 9 Manual.Count131072.C027198.packed 128 cuts27198 = true := by
 decide +kernel
def pointBounds27198 : List (Nat × Nat × Nat) := [(3568926720,103977638933429,103978021554414)]
theorem point_links_checked27198 : (cuts27198.take 1).map (fun c => (3568828417-1+2*2^9*c.k,103977285441237+c.lower,103977668062028+c.upper)) = pointBounds27198 := by
 decide +kernel
def cuts27199 : List PrefixCut := [⟨77,279976530,279976689⟩,
⟨128,468622030,468622293⟩]
theorem checked27199 : checkPrefixCuts (2^48) 3568959489 9 Manual.Count131072.C027199.packed 128 cuts27199 = true := by
 decide +kernel
def pointBounds27199 : List (Nat × Nat × Nat) := [(3569038336,103978035003446,103978417624656)]
theorem point_links_checked27199 : (cuts27199.take 1).map (fun c => (3568959489-1+2*2^9*c.k,103977755026916+c.lower,103978137647967+c.upper)) = pointBounds27199 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000224
