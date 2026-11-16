import PlattAssemblyKernel
import PlattCertificates.Count131072.C076176
import PlattCertificates.Count131072.C076177
import PlattCertificates.Count131072.C076178
import PlattCertificates.Count131072.C076179
import PlattCertificates.Count131072.C076180
import PlattCertificates.Count131072.C076181
import PlattCertificates.Count131072.C076182
import PlattCertificates.Count131072.C076183
import PlattCertificates.Count131072.C076184
import PlattCertificates.Count131072.C076185
import PlattCertificates.Count131072.C076186
import PlattCertificates.Count131072.C076187
import PlattCertificates.Count131072.C076188
import PlattCertificates.Count131072.C076189
import PlattCertificates.Count131072.C076190
import PlattCertificates.Count131072.C076191
import PlattCertificates.Count131072.C076192
import PlattCertificates.Count131072.C076193
import PlattCertificates.Count131072.C076194
import PlattCertificates.Count131072.C076195
import PlattCertificates.Count131072.C076196
import PlattCertificates.Count131072.C076197
import PlattCertificates.Count131072.C076198
import PlattCertificates.Count131072.C076199
import PlattCertificates.Count131072.C076200
import PlattCertificates.Count131072.C076201
import PlattCertificates.Count131072.C076202
import PlattCertificates.Count131072.C076203
import PlattCertificates.Count131072.C076204
import PlattCertificates.Count131072.C076205
import PlattCertificates.Count131072.C076206
import PlattCertificates.Count131072.C076207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000193
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts76176 : List PrefixCut := [⟨64,159920297,159920390⟩]
theorem checked76176 : checkPrefixCuts (2^48) 9988472833 10 Manual.Count131072.C076176.packed 64 cuts76176 = true := by
 decide +kernel
def cuts76177 : List PrefixCut := [⟨25,60106939,60106975⟩,
⟨64,158791009,158791108⟩]
theorem checked76177 : checkPrefixCuts (2^48) 9988603905 10 Manual.Count131072.C076177.packed 64 cuts76177 = true := by
 decide +kernel
def pointBounds76177 : List (Nat × Nat × Nat) := [(9988655104,116849130715580,116849520837503)]
theorem point_links_checked76177 : (cuts76177.take 1).map (fun c => (9988603905-1+2*2^10*c.k,116849070608641+c.lower,116849460730528+c.upper)) = pointBounds76177 := by
 decide +kernel
def cuts76178 : List PrefixCut := [⟨64,161296871,161296972⟩]
theorem checked76178 : checkPrefixCuts (2^48) 9988734977 10 Manual.Count131072.C076178.packed 64 cuts76178 = true := by
 decide +kernel
def cuts76179 : List PrefixCut := [⟨50,123620037,123620119⟩,
⟨64,159237705,159237810⟩]
theorem checked76179 : checkPrefixCuts (2^48) 9988866049 10 Manual.Count131072.C076179.packed 64 cuts76179 = true := by
 decide +kernel
def pointBounds76179 : List (Nat × Nat × Nat) := [(9988968448,116849514316558,116849904438727)]
theorem point_links_checked76179 : (cuts76179.take 1).map (fun c => (9988866049-1+2*2^10*c.k,116849390696521+c.lower,116849780818608+c.upper)) = pointBounds76179 := by
 decide +kernel
def cuts76180 : List PrefixCut := [⟨64,160785424,160785518⟩]
theorem checked76180 : checkPrefixCuts (2^48) 9988997121 10 Manual.Count131072.C076180.packed 64 cuts76180 = true := by
 decide +kernel
def cuts76181 : List PrefixCut := [⟨64,161234164,161234259⟩]
theorem checked76181 : checkPrefixCuts (2^48) 9989128193 10 Manual.Count131072.C076181.packed 64 cuts76181 = true := by
 decide +kernel
def cuts76182 : List PrefixCut := [⟨11,26402525,26402541⟩,
⟨64,157033589,157033687⟩]
theorem checked76182 : checkPrefixCuts (2^48) 9989259265 10 Manual.Count131072.C076182.packed 64 cuts76182 = true := by
 decide +kernel
def pointBounds76182 : List (Nat × Nat × Nat) := [(9989281792,116849898356339,116850288478736)]
theorem point_links_checked76182 : (cuts76182.take 1).map (fun c => (9989259265-1+2*2^10*c.k,116849871953814+c.lower,116850262076195+c.upper)) = pointBounds76182 := by
 decide +kernel
def cuts76183 : List PrefixCut := [⟨64,161568060,161568156⟩]
theorem checked76183 : checkPrefixCuts (2^48) 9989390337 10 Manual.Count131072.C076183.packed 64 cuts76183 = true := by
 decide +kernel
def cuts76184 : List PrefixCut := [⟨36,91659493,91659549⟩,
⟨64,161312355,161312457⟩]
theorem checked76184 : checkPrefixCuts (2^48) 9989521409 10 Manual.Count131072.C076184.packed 64 cuts76184 = true := by
 decide +kernel
def pointBounds76184 : List (Nat × Nat × Nat) := [(9989595136,116850282214956,116850672337587)]
theorem point_links_checked76184 : (cuts76184.take 1).map (fun c => (9989521409-1+2*2^10*c.k,116850190555463+c.lower,116850580678038+c.upper)) = pointBounds76184 := by
 decide +kernel
def cuts76185 : List PrefixCut := [⟨64,159647830,159647928⟩]
theorem checked76185 : checkPrefixCuts (2^48) 9989652481 10 Manual.Count131072.C076185.packed 64 cuts76185 = true := by
 decide +kernel
def cuts76186 : List PrefixCut := [⟨61,152911686,152911779⟩,
⟨64,160321951,160322050⟩]
theorem checked76186 : checkPrefixCuts (2^48) 9989783553 10 Manual.Count131072.C076186.packed 64 cuts76186 = true := by
 decide +kernel
def pointBounds76186 : List (Nat × Nat × Nat) := [(9989908480,116850664427334,116851054550202)]
theorem point_links_checked76186 : (cuts76186.take 1).map (fun c => (9989783553-1+2*2^10*c.k,116850511515648+c.lower,116850901638423+c.upper)) = pointBounds76186 := by
 decide +kernel
def cuts76187 : List PrefixCut := [⟨64,161644117,161644212⟩]
theorem checked76187 : checkPrefixCuts (2^48) 9989914625 10 Manual.Count131072.C076187.packed 64 cuts76187 = true := by
 decide +kernel
def cuts76188 : List PrefixCut := [⟨64,159669719,159669817⟩]
theorem checked76188 : checkPrefixCuts (2^48) 9990045697 10 Manual.Count131072.C076188.packed 64 cuts76188 = true := by
 decide +kernel
def cuts76189 : List PrefixCut := [⟨22,56096634,56096664⟩,
⟨64,159921203,159921295⟩]
theorem checked76189 : checkPrefixCuts (2^48) 9990176769 10 Manual.Count131072.C076189.packed 64 cuts76189 = true := by
 decide +kernel
def pointBounds76189 : List (Nat × Nat × Nat) := [(9990221824,116851049248069,116851439371166)]
theorem point_links_checked76189 : (cuts76189.take 1).map (fun c => (9990176769-1+2*2^10*c.k,116850993151435+c.lower,116851383274502+c.upper)) = pointBounds76189 := by
 decide +kernel
def cuts76190 : List PrefixCut := [⟨64,162173072,162173172⟩]
theorem checked76190 : checkPrefixCuts (2^48) 9990307841 10 Manual.Count131072.C076190.packed 64 cuts76190 = true := by
 decide +kernel
def cuts76191 : List PrefixCut := [⟨47,118839156,118839229⟩,
⟨64,162509022,162509123⟩]
theorem checked76191 : checkPrefixCuts (2^48) 9990438913 10 Manual.Count131072.C076191.packed 64 cuts76191 = true := by
 decide +kernel
def pointBounds76191 : List (Nat × Nat × Nat) := [(9990535168,116851434084866,116851824208198)]
theorem point_links_checked76191 : (cuts76191.take 1).map (fun c => (9990438913-1+2*2^10*c.k,116851315245710+c.lower,116851705368969+c.upper)) = pointBounds76191 := by
 decide +kernel
def cuts76192 : List PrefixCut := [⟨64,160027603,160027698⟩]
theorem checked76192 : checkPrefixCuts (2^48) 9990569985 10 Manual.Count131072.C076192.packed 64 cuts76192 = true := by
 decide +kernel
def cuts76193 : List PrefixCut := [⟨64,159067586,159067679⟩]
theorem checked76193 : checkPrefixCuts (2^48) 9990701057 10 Manual.Count131072.C076193.packed 64 cuts76193 = true := by
 decide +kernel
def cuts76194 : List PrefixCut := [⟨8,20763718,20763732⟩,
⟨64,160333310,160333414⟩]
theorem checked76194 : checkPrefixCuts (2^48) 9990832129 10 Manual.Count131072.C076194.packed 64 cuts76194 = true := by
 decide +kernel
def pointBounds76194 : List (Nat × Nat × Nat) := [(9990848512,116851817613639,116852207737201)]
theorem point_links_checked76194 : (cuts76194.take 1).map (fun c => (9990832129-1+2*2^10*c.k,116851796849921+c.lower,116852186973469+c.upper)) = pointBounds76194 := by
 decide +kernel
def cuts76195 : List PrefixCut := [⟨64,161852530,161852627⟩]
theorem checked76195 : checkPrefixCuts (2^48) 9990963201 10 Manual.Count131072.C076195.packed 64 cuts76195 = true := by
 decide +kernel
def cuts76196 : List PrefixCut := [⟨33,83277861,83277916⟩,
⟨64,161455990,161456099⟩]
theorem checked76196 : checkPrefixCuts (2^48) 9991094273 10 Manual.Count131072.C076196.packed 64 cuts76196 = true := by
 decide +kernel
def pointBounds76196 : List (Nat × Nat × Nat) := [(9991161856,116852202313622,116852592437426)]
theorem point_links_checked76196 : (cuts76196.take 1).map (fun c => (9991094273-1+2*2^10*c.k,116852119035761+c.lower,116852509159510+c.upper)) = pointBounds76196 := by
 decide +kernel
def cuts76197 : List PrefixCut := [⟨64,158354959,158355053⟩]
theorem checked76197 : checkPrefixCuts (2^48) 9991225345 10 Manual.Count131072.C076197.packed 64 cuts76197 = true := by
 decide +kernel
def cuts76198 : List PrefixCut := [⟨58,147985793,147985882⟩,
⟨64,163508284,163508381⟩]
theorem checked76198 : checkPrefixCuts (2^48) 9991356417 10 Manual.Count131072.C076198.packed 64 cuts76198 = true := by
 decide +kernel
def pointBounds76198 : List (Nat × Nat × Nat) := [(9991475200,116852586832503,116852976956544)]
theorem point_links_checked76198 : (cuts76198.take 1).map (fun c => (9991356417-1+2*2^10*c.k,116852438846710+c.lower,116852828970662+c.upper)) = pointBounds76198 := by
 decide +kernel
def cuts76199 : List PrefixCut := [⟨64,161844046,161844141⟩]
theorem checked76199 : checkPrefixCuts (2^48) 9991487489 10 Manual.Count131072.C076199.packed 64 cuts76199 = true := by
 decide +kernel
def cuts76200 : List PrefixCut := [⟨64,158714934,158715029⟩]
theorem checked76200 : checkPrefixCuts (2^48) 9991618561 10 Manual.Count131072.C076200.packed 64 cuts76200 = true := by
 decide +kernel
def cuts76201 : List PrefixCut := [⟨19,46087225,46087258⟩,
⟨64,158036751,158036857⟩]
theorem checked76201 : checkPrefixCuts (2^48) 9991749633 10 Manual.Count131072.C076201.packed 64 cuts76201 = true := by
 decide +kernel
def pointBounds76201 : List (Nat × Nat × Nat) := [(9991788544,116852969001199,116853359125471)]
theorem point_links_checked76201 : (cuts76201.take 1).map (fun c => (9991749633-1+2*2^10*c.k,116852922913974+c.lower,116853313038213+c.upper)) = pointBounds76201 := by
 decide +kernel
def cuts76202 : List PrefixCut := [⟨64,159527708,159527806⟩]
theorem checked76202 : checkPrefixCuts (2^48) 9991880705 10 Manual.Count131072.C076202.packed 64 cuts76202 = true := by
 decide +kernel
def cuts76203 : List PrefixCut := [⟨44,109383591,109383660⟩,
⟨64,159610131,159610226⟩]
theorem checked76203 : checkPrefixCuts (2^48) 9992011777 10 Manual.Count131072.C076203.packed 64 cuts76203 = true := by
 decide +kernel
def pointBounds76203 : List (Nat × Nat × Nat) := [(9992101888,116853349862024,116853739986536)]
theorem point_links_checked76203 : (cuts76203.take 1).map (fun c => (9992011777-1+2*2^10*c.k,116853240478433+c.lower,116853630602876+c.upper)) = pointBounds76203 := by
 decide +kernel
def cuts76204 : List PrefixCut := [⟨64,160565799,160565895⟩]
theorem checked76204 : checkPrefixCuts (2^48) 9992142849 10 Manual.Count131072.C076204.packed 64 cuts76204 = true := by
 decide +kernel
def cuts76205 : List PrefixCut := [⟨64,160028480,160028574⟩]
theorem checked76205 : checkPrefixCuts (2^48) 9992273921 10 Manual.Count131072.C076205.packed 64 cuts76205 = true := by
 decide +kernel
def cuts76206 : List PrefixCut := [⟨5,12704160,12704167⟩,
⟨64,162139030,162139132⟩]
theorem checked76206 : checkPrefixCuts (2^48) 9992404993 10 Manual.Count131072.C076206.packed 64 cuts76206 = true := by
 decide +kernel
def pointBounds76206 : List (Nat × Nat × Nat) := [(9992415232,116853733387003,116854123511738)]
theorem point_links_checked76206 : (cuts76206.take 1).map (fun c => (9992404993-1+2*2^10*c.k,116853720682843+c.lower,116854110807571+c.upper)) = pointBounds76206 := by
 decide +kernel
def cuts76207 : List PrefixCut := [⟨64,159545424,159545517⟩]
theorem checked76207 : checkPrefixCuts (2^48) 9992536065 10 Manual.Count131072.C076207.packed 64 cuts76207 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000193
