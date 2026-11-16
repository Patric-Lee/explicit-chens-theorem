import PlattAssemblyKernel
import PlattCertificates.Count131072.C045184
import PlattCertificates.Count131072.C045185
import PlattCertificates.Count131072.C045186
import PlattCertificates.Count131072.C045187
import PlattCertificates.Count131072.C045188
import PlattCertificates.Count131072.C045189
import PlattCertificates.Count131072.C045190
import PlattCertificates.Count131072.C045191
import PlattCertificates.Count131072.C045192
import PlattCertificates.Count131072.C045193
import PlattCertificates.Count131072.C045194
import PlattCertificates.Count131072.C045195
import PlattCertificates.Count131072.C045196
import PlattCertificates.Count131072.C045197
import PlattCertificates.Count131072.C045198
import PlattCertificates.Count131072.C045199
import PlattCertificates.Count131072.C045200
import PlattCertificates.Count131072.C045201
import PlattCertificates.Count131072.C045202
import PlattCertificates.Count131072.C045203
import PlattCertificates.Count131072.C045204
import PlattCertificates.Count131072.C045205
import PlattCertificates.Count131072.C045206
import PlattCertificates.Count131072.C045207
import PlattCertificates.Count131072.C045208
import PlattCertificates.Count131072.C045209
import PlattCertificates.Count131072.C045210
import PlattCertificates.Count131072.C045211
import PlattCertificates.Count131072.C045212
import PlattCertificates.Count131072.C045213
import PlattCertificates.Count131072.C045214
import PlattCertificates.Count131072.C045215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45184 : List PrefixCut := [⟨47,202663667,202663785⟩,
⟨64,274951153,274951312⟩]
theorem checked45184 : checkPrefixCuts (2^48) 5926289409 10 Manual.Count131072.C045184.packed 64 cuts45184 = true := by
 decide +kernel
def pointBounds45184 : List (Nat × Nat × Nat) := [(5926385664,110393802561242,110394188960186)]
theorem point_links_checked45184 : (cuts45184.take 1).map (fun c => (5926289409-1+2*2^10*c.k,110393599897575+c.lower,110393986296401+c.upper)) = pointBounds45184 := by
 decide +kernel
def cuts45185 : List PrefixCut := [⟨64,280976877,280977033⟩]
theorem checked45185 : checkPrefixCuts (2^48) 5926420481 10 Manual.Count131072.C045185.packed 64 cuts45185 = true := by
 decide +kernel
def cuts45186 : List PrefixCut := [⟨10,42981881,42981907⟩,
⟨64,278453518,278453675⟩]
theorem checked45186 : checkPrefixCuts (2^48) 5926551553 10 Manual.Count131072.C045186.packed 64 cuts45186 = true := by
 decide +kernel
def pointBounds45186 : List (Nat × Nat × Nat) := [(5926572032,110394198807486,110394585206653)]
theorem point_links_checked45186 : (cuts45186.take 1).map (fun c => (5926551553-1+2*2^10*c.k,110394155825605+c.lower,110394542224746+c.upper)) = pointBounds45186 := by
 decide +kernel
def cuts45187 : List PrefixCut := [⟨37,160287259,160287349⟩,
⟨64,274410524,274410677⟩]
theorem checked45187 : checkPrefixCuts (2^48) 5926682625 10 Manual.Count131072.C045187.packed 64 cuts45187 = true := by
 decide +kernel
def pointBounds45187 : List (Nat × Nat × Nat) := [(5926758400,110394594566382,110394980965770)]
theorem point_links_checked45187 : (cuts45187.take 1).map (fun c => (5926682625-1+2*2^10*c.k,110394434279123+c.lower,110394820678421+c.upper)) = pointBounds45187 := by
 decide +kernel
def cuts45188 : List PrefixCut := [⟨64,281243198,281243359⟩]
theorem checked45188 : checkPrefixCuts (2^48) 5926813697 10 Manual.Count131072.C045188.packed 64 cuts45188 = true := by
 decide +kernel
def pointBounds45188 : List (Nat × Nat × Nat) := [(5926944768,110394989932845,110395376332457)]
theorem point_links_checked45188 : (cuts45188.take 1).map (fun c => (5926813697-1+2*2^10*c.k,110394708689647+c.lower,110395095089098+c.upper)) = pointBounds45188 := by
 decide +kernel
def cuts45189 : List PrefixCut := [⟨64,278340040,278340196⟩]
theorem checked45189 : checkPrefixCuts (2^48) 5926944769 10 Manual.Count131072.C045189.packed 64 cuts45189 = true := by
 decide +kernel
def cuts45190 : List PrefixCut := [⟨27,118913577,118913644⟩,
⟨64,278001479,278001636⟩]
theorem checked45190 : checkPrefixCuts (2^48) 5927075841 10 Manual.Count131072.C045190.packed 64 cuts45190 = true := by
 decide +kernel
def pointBounds45190 : List (Nat × Nat × Nat) := [(5927131136,110395387186462,110395773586297)]
theorem point_links_checked45190 : (cuts45190.take 1).map (fun c => (5927075841-1+2*2^10*c.k,110395268272885+c.lower,110395654672653+c.upper)) = pointBounds45190 := by
 decide +kernel
def cuts45191 : List PrefixCut := [⟨54,233024494,233024634⟩,
⟨64,276665649,276665814⟩]
theorem checked45191 : checkPrefixCuts (2^48) 5927206913 10 Manual.Count131072.C045191.packed 64 cuts45191 = true := by
 decide +kernel
def pointBounds45191 : List (Nat × Nat × Nat) := [(5927317504,110395779298858,110396165698923)]
theorem point_links_checked45191 : (cuts45191.take 1).map (fun c => (5927206913-1+2*2^10*c.k,110395546274364+c.lower,110395932674289+c.upper)) = pointBounds45191 := by
 decide +kernel
def cuts45192 : List PrefixCut := [⟨64,274807535,274807690⟩]
theorem checked45192 : checkPrefixCuts (2^48) 5927337985 10 Manual.Count131072.C045192.packed 64 cuts45192 = true := by
 decide +kernel
def cuts45193 : List PrefixCut := [⟨17,75028483,75028526⟩,
⟨64,279027722,279027877⟩]
theorem checked45193 : checkPrefixCuts (2^48) 5927469057 10 Manual.Count131072.C045193.packed 64 cuts45193 = true := by
 decide +kernel
def pointBounds45193 : List (Nat × Nat × Nat) := [(5927503872,110396172776031,110396559176319)]
theorem point_links_checked45193 : (cuts45193.take 1).map (fun c => (5927469057-1+2*2^10*c.k,110396097747548+c.lower,110396484147793+c.upper)) = pointBounds45193 := by
 decide +kernel
def cuts45194 : List PrefixCut := [⟨44,189228171,189228280⟩,
⟨64,275602641,275602797⟩]
theorem checked45194 : checkPrefixCuts (2^48) 5927600129 10 Manual.Count131072.C045194.packed 64 cuts45194 = true := by
 decide +kernel
def pointBounds45194 : List (Nat × Nat × Nat) := [(5927690240,110396566003441,110396952403950)]
theorem point_links_checked45194 : (cuts45194.take 1).map (fun c => (5927600129-1+2*2^10*c.k,110396376775270+c.lower,110396763175670+c.upper)) = pointBounds45194 := by
 decide +kernel
def cuts45195 : List PrefixCut := [⟨64,275264188,275264343⟩]
theorem checked45195 : checkPrefixCuts (2^48) 5927731201 10 Manual.Count131072.C045195.packed 64 cuts45195 = true := by
 decide +kernel
def cuts45196 : List PrefixCut := [⟨7,30911638,30911656⟩,
⟨64,280718609,280718770⟩]
theorem checked45196 : checkPrefixCuts (2^48) 5927862273 10 Manual.Count131072.C045196.packed 64 cuts45196 = true := by
 decide +kernel
def pointBounds45196 : List (Nat × Nat × Nat) := [(5927876608,110396958553737,110397344954466)]
theorem point_links_checked45196 : (cuts45196.take 1).map (fun c => (5927862273-1+2*2^10*c.k,110396927642099+c.lower,110397314042810+c.upper)) = pointBounds45196 := by
 decide +kernel
def cuts45197 : List PrefixCut := [⟨34,146529582,146529676⟩,
⟨64,277151243,277151415⟩]
theorem checked45197 : checkPrefixCuts (2^48) 5927993345 10 Manual.Count131072.C045197.packed 64 cuts45197 = true := by
 decide +kernel
def pointBounds45197 : List (Nat × Nat × Nat) := [(5928062976,110397354890290,110397741291256)]
theorem point_links_checked45197 : (cuts45197.take 1).map (fun c => (5927993345-1+2*2^10*c.k,110397208360708+c.lower,110397594761580+c.upper)) = pointBounds45197 := by
 decide +kernel
def cuts45198 : List PrefixCut := [⟨61,263185935,263186091⟩,
⟨64,275673240,275673403⟩]
theorem checked45198 : checkPrefixCuts (2^48) 5928124417 10 Manual.Count131072.C045198.packed 64 cuts45198 = true := by
 decide +kernel
def pointBounds45198 : List (Nat × Nat × Nat) := [(5928249344,110397748697886,110398135099086)]
theorem point_links_checked45198 : (cuts45198.take 1).map (fun c => (5928124417-1+2*2^10*c.k,110397485511951+c.lower,110397871912995+c.upper)) = pointBounds45198 := by
 decide +kernel
def cuts45199 : List PrefixCut := [⟨64,276806639,276806799⟩]
theorem checked45199 : checkPrefixCuts (2^48) 5928255489 10 Manual.Count131072.C045199.packed 64 cuts45199 = true := by
 decide +kernel
def cuts45200 : List PrefixCut := [⟨24,105355850,105355911⟩,
⟨64,276325738,276325898⟩]
theorem checked45200 : checkPrefixCuts (2^48) 5928386561 10 Manual.Count131072.C045200.packed 64 cuts45200 = true := by
 decide +kernel
def pointBounds45200 : List (Nat × Nat × Nat) := [(5928435712,110398143347680,110398529749108)]
theorem point_links_checked45200 : (cuts45200.take 1).map (fun c => (5928386561-1+2*2^10*c.k,110398037991830+c.lower,110398424393197+c.upper)) = pointBounds45200 := by
 decide +kernel
def cuts45201 : List PrefixCut := [⟨51,219109595,219109728⟩,
⟨64,276462029,276462195⟩]
theorem checked45201 : checkPrefixCuts (2^48) 5928517633 10 Manual.Count131072.C045201.packed 64 cuts45201 = true := by
 decide +kernel
def pointBounds45201 : List (Nat × Nat × Nat) := [(5928622080,110398533427163,110398919828823)]
theorem point_links_checked45201 : (cuts45201.take 1).map (fun c => (5928517633-1+2*2^10*c.k,110398314317568+c.lower,110398700719095+c.upper)) = pointBounds45201 := by
 decide +kernel
def cuts45202 : List PrefixCut := [⟨64,275411457,275411621⟩]
theorem checked45202 : checkPrefixCuts (2^48) 5928648705 10 Manual.Count131072.C045202.packed 64 cuts45202 = true := by
 decide +kernel
def cuts45203 : List PrefixCut := [⟨14,58680222,58680256⟩,
⟨64,274028576,274028736⟩]
theorem checked45203 : checkPrefixCuts (2^48) 5928779777 10 Manual.Count131072.C045203.packed 64 cuts45203 = true := by
 decide +kernel
def pointBounds45203 : List (Nat × Nat × Nat) := [(5928808448,110398924871276,110399311273167)]
theorem point_links_checked45203 : (cuts45203.take 1).map (fun c => (5928779777-1+2*2^10*c.k,110398866191054+c.lower,110399252592911+c.upper)) = pointBounds45203 := by
 decide +kernel
def cuts45204 : List PrefixCut := [⟨41,176795546,176795648⟩,
⟨64,275446756,275446915⟩]
theorem checked45204 : checkPrefixCuts (2^48) 5928910849 10 Manual.Count131072.C045204.packed 64 cuts45204 = true := by
 decide +kernel
def pointBounds45204 : List (Nat × Nat × Nat) := [(5928994816,110399317015176,110399703417295)]
theorem point_links_checked45204 : (cuts45204.take 1).map (fun c => (5928910849-1+2*2^10*c.k,110399140219630+c.lower,110399526621647+c.upper)) = pointBounds45204 := by
 decide +kernel
def cuts45205 : List PrefixCut := [⟨64,275962860,275963018⟩]
theorem checked45205 : checkPrefixCuts (2^48) 5929041921 10 Manual.Count131072.C045205.packed 64 cuts45205 = true := by
 decide +kernel
def cuts45206 : List PrefixCut := [⟨4,19226502,19226512⟩,
⟨64,279327339,279327497⟩]
theorem checked45206 : checkPrefixCuts (2^48) 5929172993 10 Manual.Count131072.C045206.packed 64 cuts45206 = true := by
 decide +kernel
def pointBounds45206 : List (Nat × Nat × Nat) := [(5929181184,110399710855748,110400097258092)]
theorem point_links_checked45206 : (cuts45206.take 1).map (fun c => (5929172993-1+2*2^10*c.k,110399691629246+c.lower,110400078031580+c.upper)) = pointBounds45206 := by
 decide +kernel
def cuts45207 : List PrefixCut := [⟨31,134012246,134012328⟩,
⟨64,277042514,277042685⟩]
theorem checked45207 : checkPrefixCuts (2^48) 5929304065 10 Manual.Count131072.C045207.packed 64 cuts45207 = true := by
 decide +kernel
def pointBounds45207 : List (Nat × Nat × Nat) := [(5929367552,110400104968831,110400491371405)]
theorem point_links_checked45207 : (cuts45207.take 1).map (fun c => (5929304065-1+2*2^10*c.k,110399970956585+c.lower,110400357359077+c.upper)) = pointBounds45207 := by
 decide +kernel
def cuts45208 : List PrefixCut := [⟨58,247984856,247984996⟩,
⟨64,274140704,274140857⟩]
theorem checked45208 : checkPrefixCuts (2^48) 5929435137 10 Manual.Count131072.C045208.packed 64 cuts45208 = true := by
 decide +kernel
def pointBounds45208 : List (Nat × Nat × Nat) := [(5929553920,110400495983955,110400882386758)]
theorem point_links_checked45208 : (cuts45208.take 1).map (fun c => (5929435137-1+2*2^10*c.k,110400247999099+c.lower,110400634401762+c.upper)) = pointBounds45208 := by
 decide +kernel
def cuts45209 : List PrefixCut := [⟨64,279308800,279308961⟩]
theorem checked45209 : checkPrefixCuts (2^48) 5929566209 10 Manual.Count131072.C045209.packed 64 cuts45209 = true := by
 decide +kernel
def cuts45210 : List PrefixCut := [⟨21,89762950,89762998⟩,
⟨64,277641217,277641368⟩]
theorem checked45210 : checkPrefixCuts (2^48) 5929697281 10 Manual.Count131072.C045210.packed 64 cuts45210 = true := by
 decide +kernel
def pointBounds45210 : List (Nat × Nat × Nat) := [(5929740288,110400891211553,110401277614578)]
theorem point_links_checked45210 : (cuts45210.take 1).map (fun c => (5929697281-1+2*2^10*c.k,110400801448603+c.lower,110401187851580+c.upper)) = pointBounds45210 := by
 decide +kernel
def cuts45211 : List PrefixCut := [⟨48,208428636,208428754⟩,
⟨64,277872436,277872595⟩]
theorem checked45211 : checkPrefixCuts (2^48) 5929828353 10 Manual.Count131072.C045211.packed 64 cuts45211 = true := by
 decide +kernel
def pointBounds45211 : List (Nat × Nat × Nat) := [(5929926656,110401287518456,110401673921702)]
theorem point_links_checked45211 : (cuts45211.take 1).map (fun c => (5929828353-1+2*2^10*c.k,110401079089820+c.lower,110401465492948+c.upper)) = pointBounds45211 := by
 decide +kernel
def cuts45212 : List PrefixCut := [⟨64,274543669,274543832⟩]
theorem checked45212 : checkPrefixCuts (2^48) 5929959425 10 Manual.Count131072.C045212.packed 64 cuts45212 = true := by
 decide +kernel
def cuts45213 : List PrefixCut := [⟨11,46611066,46611091⟩,
⟨64,275581788,275581950⟩]
theorem checked45213 : checkPrefixCuts (2^48) 5930090497 10 Manual.Count131072.C045213.packed 64 cuts45213 = true := by
 decide +kernel
def pointBounds45213 : List (Nat × Nat × Nat) := [(5930113024,110401678116991,110402064520466)]
theorem point_links_checked45213 : (cuts45213.take 1).map (fun c => (5930090497-1+2*2^10*c.k,110401631505925+c.lower,110402017909375+c.upper)) = pointBounds45213 := by
 decide +kernel
def cuts45214 : List PrefixCut := [⟨38,161045925,161046015⟩,
⟨64,275148538,275148693⟩]
theorem checked45214 : checkPrefixCuts (2^48) 5930221569 10 Manual.Count131072.C045214.packed 64 cuts45214 = true := by
 decide +kernel
def pointBounds45214 : List (Nat × Nat × Nat) := [(5930299392,110402068133638,110402454537340)]
theorem point_links_checked45214 : (cuts45214.take 1).map (fun c => (5930221569-1+2*2^10*c.k,110401907087713+c.lower,110402293491325+c.upper)) = pointBounds45214 := by
 decide +kernel
def cuts45215 : List PrefixCut := [⟨64,281502505,281502662⟩]
theorem checked45215 : checkPrefixCuts (2^48) 5930352641 10 Manual.Count131072.C045215.packed 64 cuts45215 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000162
