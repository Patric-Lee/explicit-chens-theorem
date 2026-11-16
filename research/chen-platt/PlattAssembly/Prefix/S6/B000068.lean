import PlattAssemblyKernel
import PlattCertificates.Count131072.C052176
import PlattCertificates.Count131072.C052177
import PlattCertificates.Count131072.C052178
import PlattCertificates.Count131072.C052179
import PlattCertificates.Count131072.C052180
import PlattCertificates.Count131072.C052181
import PlattCertificates.Count131072.C052182
import PlattCertificates.Count131072.C052183
import PlattCertificates.Count131072.C052184
import PlattCertificates.Count131072.C052185
import PlattCertificates.Count131072.C052186
import PlattCertificates.Count131072.C052187
import PlattCertificates.Count131072.C052188
import PlattCertificates.Count131072.C052189
import PlattCertificates.Count131072.C052190
import PlattCertificates.Count131072.C052191
import PlattCertificates.Count131072.C052192
import PlattCertificates.Count131072.C052193
import PlattCertificates.Count131072.C052194
import PlattCertificates.Count131072.C052195
import PlattCertificates.Count131072.C052196
import PlattCertificates.Count131072.C052197
import PlattCertificates.Count131072.C052198
import PlattCertificates.Count131072.C052199
import PlattCertificates.Count131072.C052200
import PlattCertificates.Count131072.C052201
import PlattCertificates.Count131072.C052202
import PlattCertificates.Count131072.C052203
import PlattCertificates.Count131072.C052204
import PlattCertificates.Count131072.C052205
import PlattCertificates.Count131072.C052206
import PlattCertificates.Count131072.C052207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52176 : List PrefixCut := [⟨64,237345495,237345634⟩]
theorem checked52176 : checkPrefixCuts (2^48) 6842744833 10 Manual.Count131072.C052176.packed 64 cuts52176 = true := by
 decide +kernel
def cuts52177 : List PrefixCut := [⟨1,3702060,3702062⟩,
⟨64,241042953,241043085⟩]
theorem checked52177 : checkPrefixCuts (2^48) 6842875905 10 Manual.Count131072.C052177.packed 64 cuts52177 = true := by
 decide +kernel
def pointBounds52177 : List (Nat × Nat × Nat) := [(6842877952,112186778951388,112187166374770)]
theorem point_links_checked52177 : (cuts52177.take 1).map (fun c => (6842875905-1+2*2^10*c.k,112186775249328+c.lower,112187162672708+c.upper)) = pointBounds52177 := by
 decide +kernel
def cuts52178 : List PrefixCut := [⟨42,152027417,152027507⟩,
⟨64,232647243,232647379⟩]
theorem checked52178 : checkPrefixCuts (2^48) 6843006977 10 Manual.Count131072.C052178.packed 64 cuts52178 = true := by
 decide +kernel
def pointBounds52178 : List (Nat × Nat × Nat) := [(6843092992,112187168319698,112187555743300)]
theorem point_links_checked52178 : (cuts52178.take 1).map (fun c => (6843006977-1+2*2^10*c.k,112187016292281+c.lower,112187403715793+c.upper)) = pointBounds52178 := by
 decide +kernel
def cuts52179 : List PrefixCut := [⟨64,237208450,237208585⟩]
theorem checked52179 : checkPrefixCuts (2^48) 6843138049 10 Manual.Count131072.C052179.packed 64 cuts52179 = true := by
 decide +kernel
def cuts52180 : List PrefixCut := [⟨19,70334907,70334948⟩,
⟨64,236751466,236751605⟩]
theorem checked52180 : checkPrefixCuts (2^48) 6843269121 10 Manual.Count131072.C052180.packed 64 cuts52180 = true := by
 decide +kernel
def pointBounds52180 : List (Nat × Nat × Nat) := [(6843308032,112187556482881,112187943906705)]
theorem point_links_checked52180 : (cuts52180.take 1).map (fun c => (6843269121-1+2*2^10*c.k,112187486147974+c.lower,112187873571757+c.upper)) = pointBounds52180 := by
 decide +kernel
def cuts52181 : List PrefixCut := [⟨60,222680444,222680569⟩,
⟨64,238309879,238310012⟩]
theorem checked52181 : checkPrefixCuts (2^48) 6843400193 10 Manual.Count131072.C052181.packed 64 cuts52181 = true := by
 decide +kernel
def pointBounds52181 : List (Nat × Nat × Nat) := [(6843523072,112187945579884,112188333003931)]
theorem point_links_checked52181 : (cuts52181.take 1).map (fun c => (6843400193-1+2*2^10*c.k,112187722899440+c.lower,112188110323362+c.upper)) = pointBounds52181 := by
 decide +kernel
def cuts52182 : List PrefixCut := [⟨64,234274626,234274761⟩]
theorem checked52182 : checkPrefixCuts (2^48) 6843531265 10 Manual.Count131072.C052182.packed 64 cuts52182 = true := by
 decide +kernel
def cuts52183 : List PrefixCut := [⟨37,135355704,135355785⟩,
⟨64,233858842,233858978⟩]
theorem checked52183 : checkPrefixCuts (2^48) 6843662337 10 Manual.Count131072.C052183.packed 64 cuts52183 = true := by
 decide +kernel
def pointBounds52183 : List (Nat × Nat × Nat) := [(6843738112,112188330839649,112188718263920)]
theorem point_links_checked52183 : (cuts52183.take 1).map (fun c => (6843662337-1+2*2^10*c.k,112188195483945+c.lower,112188582908135+c.upper)) = pointBounds52183 := by
 decide +kernel
def cuts52184 : List PrefixCut := [⟨64,237062358,237062491⟩]
theorem checked52184 : checkPrefixCuts (2^48) 6843793409 10 Manual.Count131072.C052184.packed 64 cuts52184 = true := by
 decide +kernel
def cuts52185 : List PrefixCut := [⟨14,51080502,51080532⟩,
⟨64,237016681,237016818⟩]
theorem checked52185 : checkPrefixCuts (2^48) 6843924481 10 Manual.Count131072.C052185.packed 64 cuts52185 = true := by
 decide +kernel
def pointBounds52185 : List (Nat × Nat × Nat) := [(6843953152,112188717485647,112189104910136)]
theorem point_links_checked52185 : (cuts52185.take 1).map (fun c => (6843924481-1+2*2^10*c.k,112188666405145+c.lower,112189053829604+c.upper)) = pointBounds52185 := by
 decide +kernel
def cuts52186 : List PrefixCut := [⟨55,204234576,204234692⟩,
⟨64,237916921,237917057⟩]
theorem checked52186 : checkPrefixCuts (2^48) 6844055553 10 Manual.Count131072.C052186.packed 64 cuts52186 = true := by
 decide +kernel
def pointBounds52186 : List (Nat × Nat × Nat) := [(6844168192,112189107656402,112189495081114)]
theorem point_links_checked52186 : (cuts52186.take 1).map (fun c => (6844055553-1+2*2^10*c.k,112188903421826+c.lower,112189290846422+c.upper)) = pointBounds52186 := by
 decide +kernel
def cuts52187 : List PrefixCut := [⟨64,238159154,238159289⟩]
theorem checked52187 : checkPrefixCuts (2^48) 6844186625 10 Manual.Count131072.C052187.packed 64 cuts52187 = true := by
 decide +kernel
def cuts52188 : List PrefixCut := [⟨32,120949041,120949107⟩,
⟨64,239758443,239758577⟩]
theorem checked52188 : checkPrefixCuts (2^48) 6844317697 10 Manual.Count131072.C052188.packed 64 cuts52188 = true := by
 decide +kernel
def pointBounds52188 : List (Nat × Nat × Nat) := [(6844383232,112189500446942,112189887871875)]
theorem point_links_checked52188 : (cuts52188.take 1).map (fun c => (6844317697-1+2*2^10*c.k,112189379497901+c.lower,112189766922768+c.upper)) = pointBounds52188 := by
 decide +kernel
def cuts52189 : List PrefixCut := [⟨64,238479003,238479136⟩]
theorem checked52189 : checkPrefixCuts (2^48) 6844448769 10 Manual.Count131072.C052189.packed 64 cuts52189 = true := by
 decide +kernel
def cuts52190 : List PrefixCut := [⟨9,32076492,32076512⟩,
⟨64,236089280,236089415⟩]
theorem checked52190 : checkPrefixCuts (2^48) 6844579841 10 Manual.Count131072.C052190.packed 64 cuts52190 = true := by
 decide +kernel
def pointBounds52190 : List (Nat × Nat × Nat) := [(6844598272,112189889811839,112190277236993)]
theorem point_links_checked52190 : (cuts52190.take 1).map (fun c => (6844579841-1+2*2^10*c.k,112189857735347+c.lower,112190245160481+c.upper)) = pointBounds52190 := by
 decide +kernel
def cuts52191 : List PrefixCut := [⟨50,186614669,186614777⟩,
⟨64,238387616,238387754⟩]
theorem checked52191 : checkPrefixCuts (2^48) 6844710913 10 Manual.Count131072.C052191.packed 64 cuts52191 = true := by
 decide +kernel
def pointBounds52191 : List (Nat × Nat × Nat) := [(6844813312,112190280439296,112190667864673)]
theorem point_links_checked52191 : (cuts52191.take 1).map (fun c => (6844710913-1+2*2^10*c.k,112190093824627+c.lower,112190481249896+c.upper)) = pointBounds52191 := by
 decide +kernel
def cuts52192 : List PrefixCut := [⟨64,243070942,243071080⟩]
theorem checked52192 : checkPrefixCuts (2^48) 6844841985 10 Manual.Count131072.C052192.packed 64 cuts52192 = true := by
 decide +kernel
def cuts52193 : List PrefixCut := [⟨27,99636761,99636817⟩,
⟨64,235911242,235911376⟩]
theorem checked52193 : checkPrefixCuts (2^48) 6844973057 10 Manual.Count131072.C052193.packed 64 cuts52193 = true := by
 decide +kernel
def pointBounds52193 : List (Nat × Nat × Nat) := [(6845028352,112190674919946,112191062345547)]
theorem point_links_checked52193 : (cuts52193.take 1).map (fun c => (6844973057-1+2*2^10*c.k,112190575283185+c.lower,112190962708730+c.upper)) = pointBounds52193 := by
 decide +kernel
def cuts52194 : List PrefixCut := [⟨64,237757116,237757253⟩]
theorem checked52194 : checkPrefixCuts (2^48) 6845104129 10 Manual.Count131072.C052194.packed 64 cuts52194 = true := by
 decide +kernel
def cuts52195 : List PrefixCut := [⟨4,15337686,15337695⟩,
⟨64,238616094,238616235⟩]
theorem checked52195 : checkPrefixCuts (2^48) 6845235201 10 Manual.Count131072.C052195.packed 64 cuts52195 = true := by
 decide +kernel
def pointBounds52195 : List (Nat × Nat × Nat) := [(6845243392,112191064289229,112191451715054)]
theorem point_links_checked52195 : (cuts52195.take 1).map (fun c => (6845235201-1+2*2^10*c.k,112191048951543+c.lower,112191436377359+c.upper)) = pointBounds52195 := by
 decide +kernel
def cuts52196 : List PrefixCut := [⟨45,167929039,167929136⟩,
⟨64,237254615,237254751⟩]
theorem checked52196 : checkPrefixCuts (2^48) 6845366273 10 Manual.Count131072.C052196.packed 64 cuts52196 = true := by
 decide +kernel
def pointBounds52196 : List (Nat × Nat × Nat) := [(6845458432,112191455496676,112191842922730)]
theorem point_links_checked52196 : (cuts52196.take 1).map (fun c => (6845366273-1+2*2^10*c.k,112191287567637+c.lower,112191674993594+c.upper)) = pointBounds52196 := by
 decide +kernel
def cuts52197 : List PrefixCut := [⟨64,242554235,242554370⟩]
theorem checked52197 : checkPrefixCuts (2^48) 6845497345 10 Manual.Count131072.C052197.packed 64 cuts52197 = true := by
 decide +kernel
def cuts52198 : List PrefixCut := [⟨22,82275780,82275827⟩,
⟨64,235271900,235272036⟩]
theorem checked52198 : checkPrefixCuts (2^48) 6845628417 10 Manual.Count131072.C052198.packed 64 cuts52198 = true := by
 decide +kernel
def pointBounds52198 : List (Nat × Nat × Nat) := [(6845673472,112191849652267,112192237078542)]
theorem point_links_checked52198 : (cuts52198.take 1).map (fun c => (6845628417-1+2*2^10*c.k,112191767376487+c.lower,112192154802715+c.upper)) = pointBounds52198 := by
 decide +kernel
def cuts52199 : List PrefixCut := [⟨63,233170481,233170614⟩,
⟨64,237076491,237076627⟩]
theorem checked52199 : checkPrefixCuts (2^48) 6845759489 10 Manual.Count131072.C052199.packed 64 cuts52199 = true := by
 decide +kernel
def pointBounds52199 : List (Nat × Nat × Nat) := [(6845888512,112192235818868,112192623245365)]
theorem point_links_checked52199 : (cuts52199.take 1).map (fun c => (6845759489-1+2*2^10*c.k,112192002648387+c.lower,112192390074751+c.upper)) = pointBounds52199 := by
 decide +kernel
def cuts52200 : List PrefixCut := [⟨64,239744477,239744614⟩]
theorem checked52200 : checkPrefixCuts (2^48) 6845890561 10 Manual.Count131072.C052200.packed 64 cuts52200 = true := by
 decide +kernel
def cuts52201 : List PrefixCut := [⟨40,150439275,150439359⟩,
⟨64,238588686,238588819⟩]
theorem checked52201 : checkPrefixCuts (2^48) 6846021633 10 Manual.Count131072.C052201.packed 64 cuts52201 = true := by
 decide +kernel
def pointBounds52201 : List (Nat × Nat × Nat) := [(6846103552,112192629908630,112193017335351)]
theorem point_links_checked52201 : (cuts52201.take 1).map (fun c => (6846021633-1+2*2^10*c.k,112192479469355+c.lower,112192866895992+c.upper)) = pointBounds52201 := by
 decide +kernel
def cuts52202 : List PrefixCut := [⟨64,236528388,236528524⟩]
theorem checked52202 : checkPrefixCuts (2^48) 6846152705 10 Manual.Count131072.C052202.packed 64 cuts52202 = true := by
 decide +kernel
def cuts52203 : List PrefixCut := [⟨17,61546797,61546832⟩,
⟨64,237839460,237839596⟩]
theorem checked52203 : checkPrefixCuts (2^48) 6846283777 10 Manual.Count131072.C052203.packed 64 cuts52203 = true := by
 decide +kernel
def pointBounds52203 : List (Nat × Nat × Nat) := [(6846318592,112193016133226,112193403560167)]
theorem point_links_checked52203 : (cuts52203.take 1).map (fun c => (6846283777-1+2*2^10*c.k,112192954586429+c.lower,112193342013335+c.upper)) = pointBounds52203 := by
 decide +kernel
def cuts52204 : List PrefixCut := [⟨58,216621176,216621299⟩,
⟨64,239356110,239356245⟩]
theorem checked52204 : checkPrefixCuts (2^48) 6846414849 10 Manual.Count131072.C052204.packed 64 cuts52204 = true := by
 decide +kernel
def pointBounds52204 : List (Nat × Nat × Nat) := [(6846533632,112193409047065,112193796474230)]
theorem point_links_checked52204 : (cuts52204.take 1).map (fun c => (6846414849-1+2*2^10*c.k,112193192425889+c.lower,112193579852931+c.upper)) = pointBounds52204 := by
 decide +kernel
def cuts52205 : List PrefixCut := [⟨64,237953716,237953852⟩]
theorem checked52205 : checkPrefixCuts (2^48) 6846545921 10 Manual.Count131072.C052205.packed 64 cuts52205 = true := by
 decide +kernel
def cuts52206 : List PrefixCut := [⟨35,126457294,126457368⟩,
⟨64,233426964,233427099⟩]
theorem checked52206 : checkPrefixCuts (2^48) 6846676993 10 Manual.Count131072.C052206.packed 64 cuts52206 = true := by
 decide +kernel
def pointBounds52206 : List (Nat × Nat × Nat) := [(6846748672,112193796193009,112194183620396)]
theorem point_links_checked52206 : (cuts52206.take 1).map (fun c => (6846676993-1+2*2^10*c.k,112193669735715+c.lower,112194057163028+c.upper)) = pointBounds52206 := by
 decide +kernel
def cuts52207 : List PrefixCut := [⟨64,238396806,238396939⟩]
theorem checked52207 : checkPrefixCuts (2^48) 6846808065 10 Manual.Count131072.C052207.packed 64 cuts52207 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000068
