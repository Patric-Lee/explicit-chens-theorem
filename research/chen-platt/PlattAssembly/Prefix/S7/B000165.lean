import PlattAssemblyKernel
import PlattCertificates.Count131072.C065280
import PlattCertificates.Count131072.C065281
import PlattCertificates.Count131072.C065282
import PlattCertificates.Count131072.C065283
import PlattCertificates.Count131072.C065284
import PlattCertificates.Count131072.C065285
import PlattCertificates.Count131072.C065286
import PlattCertificates.Count131072.C065287
import PlattCertificates.Count131072.C065288
import PlattCertificates.Count131072.C065289
import PlattCertificates.Count131072.C065290
import PlattCertificates.Count131072.C065291
import PlattCertificates.Count131072.C065292
import PlattCertificates.Count131072.C065293
import PlattCertificates.Count131072.C065294
import PlattCertificates.Count131072.C065295
import PlattCertificates.Count131072.C065296
import PlattCertificates.Count131072.C065297
import PlattCertificates.Count131072.C065298
import PlattCertificates.Count131072.C065299
import PlattCertificates.Count131072.C065300
import PlattCertificates.Count131072.C065301
import PlattCertificates.Count131072.C065302
import PlattCertificates.Count131072.C065303
import PlattCertificates.Count131072.C065304
import PlattCertificates.Count131072.C065305
import PlattCertificates.Count131072.C065306
import PlattCertificates.Count131072.C065307
import PlattCertificates.Count131072.C065308
import PlattCertificates.Count131072.C065309
import PlattCertificates.Count131072.C065310
import PlattCertificates.Count131072.C065311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65280 : List PrefixCut := [⟨64,191631228,191631342⟩]
theorem checked65280 : checkPrefixCuts (2^48) 8560312321 10 Manual.Count131072.C065280.packed 64 cuts65280 = true := by
 decide +kernel
def cuts65281 : List PrefixCut := [⟨28,83484270,83484319⟩,
⟨64,188142956,188143062⟩]
theorem checked65281 : checkPrefixCuts (2^48) 8560443393 10 Manual.Count131072.C065281.packed 64 cuts65281 = true := by
 decide +kernel
def pointBounds65281 : List (Nat × Nat × Nat) := [(8560500736,114956582730910,114956971735770)]
theorem point_links_checked65281 : (cuts65281.take 1).map (fun c => (8560443393-1+2*2^10*c.k,114956499246640+c.lower,114956888251451+c.upper)) = pointBounds65281 := by
 decide +kernel
def cuts65282 : List PrefixCut := [⟨64,188567519,188567632⟩]
theorem checked65282 : checkPrefixCuts (2^48) 8560574465 10 Manual.Count131072.C065282.packed 64 cuts65282 = true := by
 decide +kernel
def cuts65283 : List PrefixCut := [⟨31,91898896,91898947⟩,
⟨64,189057816,189057919⟩]
theorem checked65283 : checkPrefixCuts (2^48) 8560705537 10 Manual.Count131072.C065283.packed 64 cuts65283 = true := by
 decide +kernel
def pointBounds65283 : List (Nat × Nat × Nat) := [(8560769024,114956967856011,114957356861092)]
theorem point_links_checked65283 : (cuts65283.take 1).map (fun c => (8560705537-1+2*2^10*c.k,114956875957115+c.lower,114957264962145+c.upper)) = pointBounds65283 := by
 decide +kernel
def cuts65284 : List PrefixCut := [⟨64,187772629,187772747⟩]
theorem checked65284 : checkPrefixCuts (2^48) 8560836609 10 Manual.Count131072.C065284.packed 64 cuts65284 = true := by
 decide +kernel
def cuts65285 : List PrefixCut := [⟨34,97518311,97518367⟩,
⟨64,183002361,183002465⟩]
theorem checked65285 : checkPrefixCuts (2^48) 8560967681 10 Manual.Count131072.C065285.packed 64 cuts65285 = true := by
 decide +kernel
def pointBounds65285 : List (Nat × Nat × Nat) := [(8561037312,114957350305871,114957739311178)]
theorem point_links_checked65285 : (cuts65285.take 1).map (fun c => (8560967681-1+2*2^10*c.k,114957252787560+c.lower,114957641792811+c.upper)) = pointBounds65285 := by
 decide +kernel
def cuts65286 : List PrefixCut := [⟨64,190890306,190890415⟩]
theorem checked65286 : checkPrefixCuts (2^48) 8561098753 10 Manual.Count131072.C065286.packed 64 cuts65286 = true := by
 decide +kernel
def cuts65287 : List PrefixCut := [⟨37,107904649,107904716⟩,
⟨64,186646165,186646277⟩]
theorem checked65287 : checkPrefixCuts (2^48) 8561229825 10 Manual.Count131072.C065287.packed 64 cuts65287 = true := by
 decide +kernel
def pointBounds65287 : List (Nat × Nat × Nat) := [(8561305600,114957734584876,114958123590407)]
theorem point_links_checked65287 : (cuts65287.take 1).map (fun c => (8561229825-1+2*2^10*c.k,114957626680227+c.lower,114958015685691+c.upper)) = pointBounds65287 := by
 decide +kernel
def cuts65288 : List PrefixCut := [⟨64,189898144,189898257⟩]
theorem checked65288 : checkPrefixCuts (2^48) 8561360897 10 Manual.Count131072.C065288.packed 64 cuts65288 = true := by
 decide +kernel
def cuts65289 : List PrefixCut := [⟨40,117534179,117534246⟩,
⟨64,190519883,190519991⟩]
theorem checked65289 : checkPrefixCuts (2^48) 8561491969 10 Manual.Count131072.C065289.packed 64 cuts65289 = true := by
 decide +kernel
def pointBounds65289 : List (Nat × Nat × Nat) := [(8561573888,114958120758715,114958509764471)]
theorem point_links_checked65289 : (cuts65289.take 1).map (fun c => (8561491969-1+2*2^10*c.k,114958003224536+c.lower,114958392230225+c.upper)) = pointBounds65289 := by
 decide +kernel
def cuts65290 : List PrefixCut := [⟨64,191010115,191010227⟩]
theorem checked65290 : checkPrefixCuts (2^48) 8561623041 10 Manual.Count131072.C065290.packed 64 cuts65290 = true := by
 decide +kernel
def cuts65291 : List PrefixCut := [⟨43,125782331,125782407⟩,
⟨64,187916883,187916996⟩]
theorem checked65291 : checkPrefixCuts (2^48) 8561754113 10 Manual.Count131072.C065291.packed 64 cuts65291 = true := by
 decide +kernel
def pointBounds65291 : List (Nat × Nat × Nat) := [(8561842176,114958510536865,114958899542850)]
theorem point_links_checked65291 : (cuts65291.take 1).map (fun c => (8561754113-1+2*2^10*c.k,114958384754534+c.lower,114958773760443+c.upper)) = pointBounds65291 := by
 decide +kernel
def cuts65292 : List PrefixCut := [⟨64,187585267,187585369⟩]
theorem checked65292 : checkPrefixCuts (2^48) 8561885185 10 Manual.Count131072.C065292.packed 64 cuts65292 = true := by
 decide +kernel
def cuts65293 : List PrefixCut := [⟨46,134555976,134556050⟩,
⟨64,187352270,187352377⟩]
theorem checked65293 : checkPrefixCuts (2^48) 8562016257 10 Manual.Count131072.C065293.packed 64 cuts65293 = true := by
 decide +kernel
def pointBounds65293 : List (Nat × Nat × Nat) := [(8562110464,114958894812660,114959283818858)]
theorem point_links_checked65293 : (cuts65293.take 1).map (fun c => (8562016257-1+2*2^10*c.k,114958760256684+c.lower,114959149262808+c.upper)) = pointBounds65293 := by
 decide +kernel
def cuts65294 : List PrefixCut := [⟨64,186231664,186231780⟩]
theorem checked65294 : checkPrefixCuts (2^48) 8562147329 10 Manual.Count131072.C065294.packed 64 cuts65294 = true := by
 decide +kernel
def cuts65295 : List PrefixCut := [⟨49,145268607,145268689⟩,
⟨64,190206528,190206633⟩]
theorem checked65295 : checkPrefixCuts (2^48) 8562278401 10 Manual.Count131072.C065295.packed 64 cuts65295 = true := by
 decide +kernel
def pointBounds65295 : List (Nat × Nat × Nat) := [(8562378752,114959279109225,114959668115654)]
theorem point_links_checked65295 : (cuts65295.take 1).map (fun c => (8562278401-1+2*2^10*c.k,114959133840618+c.lower,114959522846965+c.upper)) = pointBounds65295 := by
 decide +kernel
def cuts65296 : List PrefixCut := [⟨64,187606654,187606760⟩]
theorem checked65296 : checkPrefixCuts (2^48) 8562409473 10 Manual.Count131072.C065296.packed 64 cuts65296 = true := by
 decide +kernel
def cuts65297 : List PrefixCut := [⟨52,152594699,152594790⟩,
⟨64,186420366,186420478⟩]
theorem checked65297 : checkPrefixCuts (2^48) 8562540545 10 Manual.Count131072.C065297.packed 64 cuts65297 = true := by
 decide +kernel
def pointBounds65297 : List (Nat × Nat × Nat) := [(8562647040,114959664248499,114960053255148)]
theorem point_links_checked65297 : (cuts65297.take 1).map (fun c => (8562540545-1+2*2^10*c.k,114959511653800+c.lower,114959900660358+c.upper)) = pointBounds65297 := by
 decide +kernel
def cuts65298 : List PrefixCut := [⟨64,189934817,189934930⟩]
theorem checked65298 : checkPrefixCuts (2^48) 8562671617 10 Manual.Count131072.C065298.packed 64 cuts65298 = true := by
 decide +kernel
def cuts65299 : List PrefixCut := [⟨55,161826902,161826999⟩,
⟨64,188584182,188584292⟩]
theorem checked65299 : checkPrefixCuts (2^48) 8562802689 10 Manual.Count131072.C065299.packed 64 cuts65299 = true := by
 decide +kernel
def pointBounds65299 : List (Nat × Nat × Nat) := [(8562915328,114960049835885,114960438842765)]
theorem point_links_checked65299 : (cuts65299.take 1).map (fun c => (8562802689-1+2*2^10*c.k,114959888008983+c.lower,114960277015766+c.upper)) = pointBounds65299 := by
 decide +kernel
def cuts65300 : List PrefixCut := [⟨64,187036346,187036456⟩]
theorem checked65300 : checkPrefixCuts (2^48) 8562933761 10 Manual.Count131072.C065300.packed 64 cuts65300 = true := by
 decide +kernel
def cuts65301 : List PrefixCut := [⟨58,171222878,171222975⟩,
⟨64,188611284,188611391⟩]
theorem checked65301 : checkPrefixCuts (2^48) 8563064833 10 Manual.Count131072.C065301.packed 64 cuts65301 = true := by
 decide +kernel
def pointBounds65301 : List (Nat × Nat × Nat) := [(8563183616,114960434852389,114960823859489)]
theorem point_links_checked65301 : (cuts65301.take 1).map (fun c => (8563064833-1+2*2^10*c.k,114960263629511+c.lower,114960652636514+c.upper)) = pointBounds65301 := by
 decide +kernel
def cuts65302 : List PrefixCut := [⟨64,190843545,190843658⟩]
theorem checked65302 : checkPrefixCuts (2^48) 8563195905 10 Manual.Count131072.C065302.packed 64 cuts65302 = true := by
 decide +kernel
def cuts65303 : List PrefixCut := [⟨61,180322441,180322545⟩,
⟨64,189558719,189558828⟩]
theorem checked65303 : checkPrefixCuts (2^48) 8563326977 10 Manual.Count131072.C065303.packed 64 cuts65303 = true := by
 decide +kernel
def pointBounds65303 : List (Nat × Nat × Nat) := [(8563451904,114960823406781,114961212414108)]
theorem point_links_checked65303 : (cuts65303.take 1).map (fun c => (8563326977-1+2*2^10*c.k,114960643084340+c.lower,114961032091563+c.upper)) = pointBounds65303 := by
 decide +kernel
def cuts65304 : List PrefixCut := [⟨64,188865566,188865676⟩]
theorem checked65304 : checkPrefixCuts (2^48) 8563458049 10 Manual.Count131072.C065304.packed 64 cuts65304 = true := by
 decide +kernel
def cuts65305 : List PrefixCut := [⟨64,189158506,189158616⟩]
theorem checked65305 : checkPrefixCuts (2^48) 8563589121 10 Manual.Count131072.C065305.packed 64 cuts65305 = true := by
 decide +kernel
def pointBounds65305 : List (Nat × Nat × Nat) := [(8563720192,114961210667131,114961599674683)]
theorem point_links_checked65305 : (cuts65305.take 1).map (fun c => (8563589121-1+2*2^10*c.k,114961021508625+c.lower,114961410516067+c.upper)) = pointBounds65305 := by
 decide +kernel
def cuts65306 : List PrefixCut := [⟨64,190963338,190963447⟩]
theorem checked65306 : checkPrefixCuts (2^48) 8563720193 10 Manual.Count131072.C065306.packed 64 cuts65306 = true := by
 decide +kernel
def cuts65307 : List PrefixCut := [⟨64,187936602,187936720⟩]
theorem checked65307 : checkPrefixCuts (2^48) 8563851265 10 Manual.Count131072.C065307.packed 64 cuts65307 = true := by
 decide +kernel
def cuts65308 : List PrefixCut := [⟨3,8414024,8414027⟩,
⟨64,185238629,185238735⟩]
theorem checked65308 : checkPrefixCuts (2^48) 8563982337 10 Manual.Count131072.C065308.packed 64 cuts65308 = true := by
 decide +kernel
def pointBounds65308 : List (Nat × Nat × Nat) := [(8563988480,114961597981095,114961986988877)]
theorem point_links_checked65308 : (cuts65308.take 1).map (fun c => (8563982337-1+2*2^10*c.k,114961589567071+c.lower,114961978574850+c.upper)) = pointBounds65308 := by
 decide +kernel
def cuts65309 : List PrefixCut := [⟨64,188686793,188686905⟩]
theorem checked65309 : checkPrefixCuts (2^48) 8564113409 10 Manual.Count131072.C065309.packed 64 cuts65309 = true := by
 decide +kernel
def cuts65310 : List PrefixCut := [⟨6,17912112,17912122⟩,
⟨64,189374077,189374185⟩]
theorem checked65310 : checkPrefixCuts (2^48) 8564244481 10 Manual.Count131072.C065310.packed 64 cuts65310 = true := by
 decide +kernel
def pointBounds65310 : List (Nat × Nat × Nat) := [(8564256768,114961981404605,114962370412612)]
theorem point_links_checked65310 : (cuts65310.take 1).map (fun c => (8564244481-1+2*2^10*c.k,114961963492493+c.lower,114962352500490+c.upper)) = pointBounds65310 := by
 decide +kernel
def cuts65311 : List PrefixCut := [⟨64,188352346,188352453⟩]
theorem checked65311 : checkPrefixCuts (2^48) 8564375553 10 Manual.Count131072.C065311.packed 64 cuts65311 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000165
