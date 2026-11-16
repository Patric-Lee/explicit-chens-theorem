import PlattAssemblyKernel
import PlattCertificates.Count131072.C068160
import PlattCertificates.Count131072.C068161
import PlattCertificates.Count131072.C068162
import PlattCertificates.Count131072.C068163
import PlattCertificates.Count131072.C068164
import PlattCertificates.Count131072.C068165
import PlattCertificates.Count131072.C068166
import PlattCertificates.Count131072.C068167
import PlattCertificates.Count131072.C068168
import PlattCertificates.Count131072.C068169
import PlattCertificates.Count131072.C068170
import PlattCertificates.Count131072.C068171
import PlattCertificates.Count131072.C068172
import PlattCertificates.Count131072.C068173
import PlattCertificates.Count131072.C068174
import PlattCertificates.Count131072.C068175
import PlattCertificates.Count131072.C068176
import PlattCertificates.Count131072.C068177
import PlattCertificates.Count131072.C068178
import PlattCertificates.Count131072.C068179
import PlattCertificates.Count131072.C068180
import PlattCertificates.Count131072.C068181
import PlattCertificates.Count131072.C068182
import PlattCertificates.Count131072.C068183
import PlattCertificates.Count131072.C068184
import PlattCertificates.Count131072.C068185
import PlattCertificates.Count131072.C068186
import PlattCertificates.Count131072.C068187
import PlattCertificates.Count131072.C068188
import PlattCertificates.Count131072.C068189
import PlattCertificates.Count131072.C068190
import PlattCertificates.Count131072.C068191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000255
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68160 : List PrefixCut := [⟨64,178908366,178908472⟩]
theorem checked68160 : checkPrefixCuts (2^48) 8937799681 10 Manual.Count131072.C068160.packed 64 cuts68160 = true := by
 decide +kernel
def cuts68161 : List PrefixCut := [⟨62,174213483,174213580⟩,
⟨64,179756026,179756127⟩]
theorem checked68161 : checkPrefixCuts (2^48) 8937930753 10 Manual.Count131072.C068161.packed 64 cuts68161 = true := by
 decide +kernel
def pointBounds68161 : List (Nat × Nat × Nat) := [(8938057728,115487215157943,115487604471620)]
theorem point_links_checked68161 : (cuts68161.take 1).map (fun c => (8937930753-1+2*2^10*c.k,115487040944460+c.lower,115487430258040+c.upper)) = pointBounds68161 := by
 decide +kernel
def cuts68162 : List PrefixCut := [⟨64,179092065,179092175⟩]
theorem checked68162 : checkPrefixCuts (2^48) 8938061825 10 Manual.Count131072.C068162.packed 64 cuts68162 = true := by
 decide +kernel
def cuts68163 : List PrefixCut := [⟨64,179908203,179908312⟩]
theorem checked68163 : checkPrefixCuts (2^48) 8938192897 10 Manual.Count131072.C068163.packed 64 cuts68163 = true := by
 decide +kernel
def cuts68164 : List PrefixCut := [⟨7,19870674,19870685⟩,
⟨64,178960864,178960963⟩]
theorem checked68164 : checkPrefixCuts (2^48) 8938323969 10 Manual.Count131072.C068164.packed 64 cuts68164 = true := by
 decide +kernel
def pointBounds68164 : List (Nat × Nat × Nat) := [(8938338304,115487599571428,115487988885339)]
theorem point_links_checked68164 : (cuts68164.take 1).map (fun c => (8938323969-1+2*2^10*c.k,115487579700754+c.lower,115487969014654+c.upper)) = pointBounds68164 := by
 decide +kernel
def cuts68165 : List PrefixCut := [⟨64,182611091,182611190⟩]
theorem checked68165 : checkPrefixCuts (2^48) 8938455041 10 Manual.Count131072.C068165.packed 64 cuts68165 = true := by
 decide +kernel
def cuts68166 : List PrefixCut := [⟨16,45093409,45093436⟩,
⟨64,179774334,179774447⟩]
theorem checked68166 : checkPrefixCuts (2^48) 8938586113 10 Manual.Count131072.C068166.packed 64 cuts68166 = true := by
 decide +kernel
def pointBounds68166 : List (Nat × Nat × Nat) := [(8938618880,115487986366118,115488375680243)]
theorem point_links_checked68166 : (cuts68166.take 1).map (fun c => (8938586113-1+2*2^10*c.k,115487941272709+c.lower,115488330586807+c.upper)) = pointBounds68166 := by
 decide +kernel
def cuts68167 : List PrefixCut := [⟨64,179771699,179771801⟩]
theorem checked68167 : checkPrefixCuts (2^48) 8938717185 10 Manual.Count131072.C068167.packed 64 cuts68167 = true := by
 decide +kernel
def cuts68168 : List PrefixCut := [⟨25,70377590,70377630⟩,
⟨64,181186051,181186152⟩]
theorem checked68168 : checkPrefixCuts (2^48) 8938848257 10 Manual.Count131072.C068168.packed 64 cuts68168 = true := by
 decide +kernel
def pointBounds68168 : List (Nat × Nat × Nat) := [(8938899456,115488371196332,115488760510685)]
theorem point_links_checked68168 : (cuts68168.take 1).map (fun c => (8938848257-1+2*2^10*c.k,115488300818742+c.lower,115488690133055+c.upper)) = pointBounds68168 := by
 decide +kernel
def cuts68169 : List PrefixCut := [⟨64,179955352,179955459⟩]
theorem checked68169 : checkPrefixCuts (2^48) 8938979329 10 Manual.Count131072.C068169.packed 64 cuts68169 = true := by
 decide +kernel
def cuts68170 : List PrefixCut := [⟨34,93770962,93771014⟩,
⟨64,181054771,181054872⟩]
theorem checked68170 : checkPrefixCuts (2^48) 8939110401 10 Manual.Count131072.C068170.packed 64 cuts68170 = true := by
 decide +kernel
def pointBounds68170 : List (Nat × Nat × Nat) := [(8939180032,115488755731107,115489145045680)]
theorem point_links_checked68170 : (cuts68170.take 1).map (fun c => (8939110401-1+2*2^10*c.k,115488661960145+c.lower,115489051274666+c.upper)) = pointBounds68170 := by
 decide +kernel
def cuts68171 : List PrefixCut := [⟨64,178753572,178753680⟩]
theorem checked68171 : checkPrefixCuts (2^48) 8939241473 10 Manual.Count131072.C068171.packed 64 cuts68171 = true := by
 decide +kernel
def cuts68172 : List PrefixCut := [⟨43,121224720,121224787⟩,
⟨64,178719453,178719555⟩]
theorem checked68172 : checkPrefixCuts (2^48) 8939372545 10 Manual.Count131072.C068172.packed 64 cuts68172 = true := by
 decide +kernel
def pointBounds68172 : List (Nat × Nat × Nat) := [(8939460608,115489142993208,115489532308005)]
theorem point_links_checked68172 : (cuts68172.take 1).map (fun c => (8939372545-1+2*2^10*c.k,115489021768488+c.lower,115489411083218+c.upper)) = pointBounds68172 := by
 decide +kernel
def cuts68173 : List PrefixCut := [⟨64,180763455,180763561⟩]
theorem checked68173 : checkPrefixCuts (2^48) 8939503617 10 Manual.Count131072.C068173.packed 64 cuts68173 = true := by
 decide +kernel
def cuts68174 : List PrefixCut := [⟨52,146850648,146850731⟩,
⟨64,179721778,179721878⟩]
theorem checked68174 : checkPrefixCuts (2^48) 8939634689 10 Manual.Count131072.C068174.packed 64 cuts68174 = true := by
 decide +kernel
def pointBounds68174 : List (Nat × Nat × Nat) := [(8939741184,115489528102044,115489917417065)]
theorem point_links_checked68174 : (cuts68174.take 1).map (fun c => (8939634689-1+2*2^10*c.k,115489381251396+c.lower,115489770566334+c.upper)) = pointBounds68174 := by
 decide +kernel
def cuts68175 : List PrefixCut := [⟨64,180978548,180978652⟩]
theorem checked68175 : checkPrefixCuts (2^48) 8939765761 10 Manual.Count131072.C068175.packed 64 cuts68175 = true := by
 decide +kernel
def cuts68176 : List PrefixCut := [⟨61,170963726,170963824⟩,
⟨64,179559077,179559179⟩]
theorem checked68176 : checkPrefixCuts (2^48) 8939896833 10 Manual.Count131072.C068176.packed 64 cuts68176 = true := by
 decide +kernel
def pointBounds68176 : List (Nat × Nat × Nat) := [(8940021760,115489912915448,115490302230688)]
theorem point_links_checked68176 : (cuts68176.take 1).map (fun c => (8939896833-1+2*2^10*c.k,115489741951722+c.lower,115490131266864+c.upper)) = pointBounds68176 := by
 decide +kernel
def cuts68177 : List PrefixCut := [⟨64,182830825,182830931⟩]
theorem checked68177 : checkPrefixCuts (2^48) 8940027905 10 Manual.Count131072.C068177.packed 64 cuts68177 = true := by
 decide +kernel
def cuts68178 : List PrefixCut := [⟨64,178105549,178105648⟩]
theorem checked68178 : checkPrefixCuts (2^48) 8940158977 10 Manual.Count131072.C068178.packed 64 cuts68178 = true := by
 decide +kernel
def cuts68179 : List PrefixCut := [⟨6,16654954,16654964⟩,
⟨64,178732594,178732700⟩]
theorem checked68179 : checkPrefixCuts (2^48) 8940290049 10 Manual.Count131072.C068179.packed 64 cuts68179 = true := by
 decide +kernel
def pointBounds68179 : List (Nat × Nat × Nat) := [(8940302336,115490299102127,115490688417586)]
theorem point_links_checked68179 : (cuts68179.take 1).map (fun c => (8940290049-1+2*2^10*c.k,115490282447173+c.lower,115490671762622+c.upper)) = pointBounds68179 := by
 decide +kernel
def cuts68180 : List PrefixCut := [⟨64,179139259,179139360⟩]
theorem checked68180 : checkPrefixCuts (2^48) 8940421121 10 Manual.Count131072.C068180.packed 64 cuts68180 = true := by
 decide +kernel
def cuts68181 : List PrefixCut := [⟨15,42564867,42564890⟩,
⟨64,179545904,179546008⟩]
theorem checked68181 : checkPrefixCuts (2^48) 8940552193 10 Manual.Count131072.C068181.packed 64 cuts68181 = true := by
 decide +kernel
def pointBounds68181 : List (Nat × Nat × Nat) := [(8940582912,115490682883893,115491072199572)]
theorem point_links_checked68181 : (cuts68181.take 1).map (fun c => (8940552193-1+2*2^10*c.k,115490640319026+c.lower,115491029634682+c.upper)) = pointBounds68181 := by
 decide +kernel
def cuts68182 : List PrefixCut := [⟨64,179543283,179543391⟩]
theorem checked68182 : checkPrefixCuts (2^48) 8940683265 10 Manual.Count131072.C068182.packed 64 cuts68182 = true := by
 decide +kernel
def cuts68183 : List PrefixCut := [⟨24,67843570,67843610⟩,
⟨64,181524000,181524108⟩]
theorem checked68183 : checkPrefixCuts (2^48) 8940814337 10 Manual.Count131072.C068183.packed 64 cuts68183 = true := by
 decide +kernel
def pointBounds68183 : List (Nat × Nat × Nat) := [(8940863488,115491067251783,115491456567691)]
theorem point_links_checked68183 : (cuts68183.take 1).map (fun c => (8940814337-1+2*2^10*c.k,115490999408213+c.lower,115491388724081+c.upper)) = pointBounds68183 := by
 decide +kernel
def cuts68184 : List PrefixCut := [⟨64,178688008,178688110⟩]
theorem checked68184 : checkPrefixCuts (2^48) 8940945409 10 Manual.Count131072.C068184.packed 64 cuts68184 = true := by
 decide +kernel
def cuts68185 : List PrefixCut := [⟨33,93152215,93152269⟩,
⟨64,180322407,180322509⟩]
theorem checked68185 : checkPrefixCuts (2^48) 8941076481 10 Manual.Count131072.C068185.packed 64 cuts68185 = true := by
 decide +kernel
def pointBounds68185 : List (Nat × Nat × Nat) := [(8941144064,115491452772436,115491842088568)]
theorem point_links_checked68185 : (cuts68185.take 1).map (fun c => (8941076481-1+2*2^10*c.k,115491359620221+c.lower,115491748936299+c.upper)) = pointBounds68185 := by
 decide +kernel
def cuts68186 : List PrefixCut := [⟨64,179217937,179218043⟩]
theorem checked68186 : checkPrefixCuts (2^48) 8941207553 10 Manual.Count131072.C068186.packed 64 cuts68186 = true := by
 decide +kernel
def cuts68187 : List PrefixCut := [⟨42,119025965,119026032⟩,
⟨64,178963488,178963589⟩]
theorem checked68187 : checkPrefixCuts (2^48) 8941338625 10 Manual.Count131072.C068187.packed 64 cuts68187 = true := by
 decide +kernel
def pointBounds68187 : List (Nat × Nat × Nat) := [(8941424640,115491838186530,115492227502883)]
theorem point_links_checked68187 : (cuts68187.take 1).map (fun c => (8941338625-1+2*2^10*c.k,115491719160565+c.lower,115492108476851+c.upper)) = pointBounds68187 := by
 decide +kernel
def cuts68188 : List PrefixCut := [⟨64,179590453,179590555⟩]
theorem checked68188 : checkPrefixCuts (2^48) 8941469697 10 Manual.Count131072.C068188.packed 64 cuts68188 = true := by
 decide +kernel
def cuts68189 : List PrefixCut := [⟨51,142977920,142977996⟩,
⟨64,180217384,180217479⟩]
theorem checked68189 : checkPrefixCuts (2^48) 8941600769 10 Manual.Count131072.C068189.packed 64 cuts68189 = true := by
 decide +kernel
def pointBounds68189 : List (Nat × Nat × Nat) := [(8941705216,115492220692426,115492610008991)]
theorem point_links_checked68189 : (cuts68189.take 1).map (fun c => (8941600769-1+2*2^10*c.k,115492077714506+c.lower,115492467030995+c.upper)) = pointBounds68189 := by
 decide +kernel
def cuts68190 : List PrefixCut := [⟨64,179364834,179364930⟩]
theorem checked68190 : checkPrefixCuts (2^48) 8941731841 10 Manual.Count131072.C068190.packed 64 cuts68190 = true := by
 decide +kernel
def cuts68191 : List PrefixCut := [⟨60,172059349,172059444⟩,
⟨64,183328431,183328531⟩]
theorem checked68191 : checkPrefixCuts (2^48) 8941862913 10 Manual.Count131072.C068191.packed 64 cuts68191 = true := by
 decide +kernel
def pointBounds68191 : List (Nat × Nat × Nat) := [(8941985792,115492609356073,115492998672848)]
theorem point_links_checked68191 : (cuts68191.take 1).map (fun c => (8941862913-1+2*2^10*c.k,115492437296724+c.lower,115492826613404+c.upper)) = pointBounds68191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000255
