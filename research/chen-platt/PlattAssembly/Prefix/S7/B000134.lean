import PlattAssemblyKernel
import PlattCertificates.Count131072.C064288
import PlattCertificates.Count131072.C064289
import PlattCertificates.Count131072.C064290
import PlattCertificates.Count131072.C064291
import PlattCertificates.Count131072.C064292
import PlattCertificates.Count131072.C064293
import PlattCertificates.Count131072.C064294
import PlattCertificates.Count131072.C064295
import PlattCertificates.Count131072.C064296
import PlattCertificates.Count131072.C064297
import PlattCertificates.Count131072.C064298
import PlattCertificates.Count131072.C064299
import PlattCertificates.Count131072.C064300
import PlattCertificates.Count131072.C064301
import PlattCertificates.Count131072.C064302
import PlattCertificates.Count131072.C064303
import PlattCertificates.Count131072.C064304
import PlattCertificates.Count131072.C064305
import PlattCertificates.Count131072.C064306
import PlattCertificates.Count131072.C064307
import PlattCertificates.Count131072.C064308
import PlattCertificates.Count131072.C064309
import PlattCertificates.Count131072.C064310
import PlattCertificates.Count131072.C064311
import PlattCertificates.Count131072.C064312
import PlattCertificates.Count131072.C064313
import PlattCertificates.Count131072.C064314
import PlattCertificates.Count131072.C064315
import PlattCertificates.Count131072.C064316
import PlattCertificates.Count131072.C064317
import PlattCertificates.Count131072.C064318
import PlattCertificates.Count131072.C064319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000134
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64288 : List PrefixCut := [⟨64,191682023,191682137⟩]
theorem checked64288 : checkPrefixCuts (2^48) 8430288897 10 Manual.Count131072.C064288.packed 64 cuts64288 = true := by
 decide +kernel
def cuts64289 : List PrefixCut := [⟨14,42302530,42302555⟩,
⟨64,191144837,191144944⟩]
theorem checked64289 : checkPrefixCuts (2^48) 8430419969 10 Manual.Count131072.C064289.packed 64 cuts64289 = true := by
 decide +kernel
def pointBounds64289 : List (Nat × Nat × Nat) := [(8430448640,114768108503364,114768497399196)]
theorem point_links_checked64289 : (cuts64289.take 1).map (fun c => (8430419969-1+2*2^10*c.k,114768066200834+c.lower,114768455096641+c.upper)) = pointBounds64289 := by
 decide +kernel
def cuts64290 : List PrefixCut := [⟨64,190974921,190975031⟩]
theorem checked64290 : checkPrefixCuts (2^48) 8430551041 10 Manual.Count131072.C064290.packed 64 cuts64290 = true := by
 decide +kernel
def cuts64291 : List PrefixCut := [⟨15,44705064,44705091⟩,
⟨64,190537929,190538041⟩]
theorem checked64291 : checkPrefixCuts (2^48) 8430682113 10 Manual.Count131072.C064291.packed 64 cuts64291 = true := by
 decide +kernel
def pointBounds64291 : List (Nat × Nat × Nat) := [(8430712832,114768493025656,114768881921707)]
theorem point_links_checked64291 : (cuts64291.take 1).map (fun c => (8430682113-1+2*2^10*c.k,114768448320592+c.lower,114768837216616+c.upper)) = pointBounds64291 := by
 decide +kernel
def cuts64292 : List PrefixCut := [⟨64,190868834,190868947⟩]
theorem checked64292 : checkPrefixCuts (2^48) 8430813185 10 Manual.Count131072.C064292.packed 64 cuts64292 = true := by
 decide +kernel
def cuts64293 : List PrefixCut := [⟨16,47775171,47775195⟩,
⟨64,191233106,191233213⟩]
theorem checked64293 : checkPrefixCuts (2^48) 8430944257 10 Manual.Count131072.C064293.packed 64 cuts64293 = true := by
 decide +kernel
def pointBounds64293 : List (Nat × Nat × Nat) := [(8430977024,114768877502526,114769266398799)]
theorem point_links_checked64293 : (cuts64293.take 1).map (fun c => (8430944257-1+2*2^10*c.k,114768829727355+c.lower,114769218623604+c.upper)) = pointBounds64293 := by
 decide +kernel
def cuts64294 : List PrefixCut := [⟨64,192198298,192198409⟩]
theorem checked64294 : checkPrefixCuts (2^48) 8431075329 10 Manual.Count131072.C064294.packed 64 cuts64294 = true := by
 decide +kernel
def cuts64295 : List PrefixCut := [⟨17,50143999,50144028⟩,
⟨64,189357618,189357727⟩]
theorem checked64295 : checkPrefixCuts (2^48) 8431206401 10 Manual.Count131072.C064295.packed 64 cuts64295 = true := by
 decide +kernel
def pointBounds64295 : List (Nat × Nat × Nat) := [(8431241216,114769263302758,114769652199254)]
theorem point_links_checked64295 : (cuts64295.take 1).map (fun c => (8431206401-1+2*2^10*c.k,114769213158759+c.lower,114769602055226+c.upper)) = pointBounds64295 := by
 decide +kernel
def cuts64296 : List PrefixCut := [⟨64,192559546,192559658⟩]
theorem checked64296 : checkPrefixCuts (2^48) 8431337473 10 Manual.Count131072.C064296.packed 64 cuts64296 = true := by
 decide +kernel
def cuts64297 : List PrefixCut := [⟨18,54782781,54782811⟩,
⟨64,192990551,192990660⟩]
theorem checked64297 : checkPrefixCuts (2^48) 8431468545 10 Manual.Count131072.C064297.packed 64 cuts64297 = true := by
 decide +kernel
def pointBounds64297 : List (Nat × Nat × Nat) := [(8431505408,114769649858704,114770038755422)]
theorem point_links_checked64297 : (cuts64297.take 1).map (fun c => (8431468545-1+2*2^10*c.k,114769595075923+c.lower,114769983972611+c.upper)) = pointBounds64297 := by
 decide +kernel
def cuts64298 : List PrefixCut := [⟨64,191385160,191385274⟩]
theorem checked64298 : checkPrefixCuts (2^48) 8431599617 10 Manual.Count131072.C064298.packed 64 cuts64298 = true := by
 decide +kernel
def cuts64299 : List PrefixCut := [⟨19,57218012,57218045⟩,
⟨64,190247186,190247292⟩]
theorem checked64299 : checkPrefixCuts (2^48) 8431730689 10 Manual.Count131072.C064299.packed 64 cuts64299 = true := by
 decide +kernel
def pointBounds64299 : List (Nat × Nat × Nat) := [(8431769600,114770036669646,114770425566590)]
theorem point_links_checked64299 : (cuts64299.take 1).map (fun c => (8431730689-1+2*2^10*c.k,114769979451634+c.lower,114770368348545+c.upper)) = pointBounds64299 := by
 decide +kernel
def cuts64300 : List PrefixCut := [⟨64,195819024,195819139⟩]
theorem checked64300 : checkPrefixCuts (2^48) 8431861761 10 Manual.Count131072.C064300.packed 64 cuts64300 = true := by
 decide +kernel
def cuts64301 : List PrefixCut := [⟨20,59419417,59419452⟩,
⟨64,191075798,191075908⟩]
theorem checked64301 : checkPrefixCuts (2^48) 8431992833 10 Manual.Count131072.C064301.packed 64 cuts64301 = true := by
 decide +kernel
def pointBounds64301 : List (Nat × Nat × Nat) := [(8432033792,114770424937261,114770813834428)]
theorem point_links_checked64301 : (cuts64301.take 1).map (fun c => (8431992833-1+2*2^10*c.k,114770365517844+c.lower,114770754414976+c.upper)) = pointBounds64301 := by
 decide +kernel
def cuts64302 : List PrefixCut := [⟨64,192675130,192675238⟩]
theorem checked64302 : checkPrefixCuts (2^48) 8432123905 10 Manual.Count131072.C064302.packed 64 cuts64302 = true := by
 decide +kernel
def cuts64303 : List PrefixCut := [⟨21,63890570,63890606⟩,
⟨64,192705506,192705615⟩]
theorem checked64303 : checkPrefixCuts (2^48) 8432254977 10 Manual.Count131072.C064303.packed 64 cuts64303 = true := by
 decide +kernel
def pointBounds64303 : List (Nat × Nat × Nat) := [(8432297984,114770813159342,114771202056728)]
theorem point_links_checked64303 : (cuts64303.take 1).map (fun c => (8432254977-1+2*2^10*c.k,114770749268772+c.lower,114771138166122+c.upper)) = pointBounds64303 := by
 decide +kernel
def cuts64304 : List PrefixCut := [⟨64,191567586,191567695⟩]
theorem checked64304 : checkPrefixCuts (2^48) 8432386049 10 Manual.Count131072.C064304.packed 64 cuts64304 = true := by
 decide +kernel
def cuts64305 : List PrefixCut := [⟨22,67994269,67994307⟩,
⟨64,192933178,192933291⟩]
theorem checked64305 : checkPrefixCuts (2^48) 8432517121 10 Manual.Count131072.C064305.packed 64 cuts64305 = true := by
 decide +kernel
def pointBounds64305 : List (Nat × Nat × Nat) := [(8432562176,114771201536133,114771590433739)]
theorem point_links_checked64305 : (cuts64305.take 1).map (fun c => (8432517121-1+2*2^10*c.k,114771133541864+c.lower,114771522439432+c.upper)) = pointBounds64305 := by
 decide +kernel
def cuts64306 : List PrefixCut := [⟨64,189959453,189959562⟩]
theorem checked64306 : checkPrefixCuts (2^48) 8432648193 10 Manual.Count131072.C064306.packed 64 cuts64306 = true := by
 decide +kernel
def cuts64307 : List PrefixCut := [⟨23,67090925,67090964⟩,
⟨64,190557294,190557409⟩]
theorem checked64307 : checkPrefixCuts (2^48) 8432779265 10 Manual.Count131072.C064307.packed 64 cuts64307 = true := by
 decide +kernel
def pointBounds64307 : List (Nat × Nat × Nat) := [(8432826368,114771583525420,114771972423249)]
theorem point_links_checked64307 : (cuts64307.take 1).map (fun c => (8432779265-1+2*2^10*c.k,114771516434495+c.lower,114771905332285+c.upper)) = pointBounds64307 := by
 decide +kernel
def cuts64308 : List PrefixCut := [⟨64,189452868,189452979⟩]
theorem checked64308 : checkPrefixCuts (2^48) 8432910337 10 Manual.Count131072.C064308.packed 64 cuts64308 = true := by
 decide +kernel
def cuts64309 : List PrefixCut := [⟨24,73997978,73998020⟩,
⟨64,191953243,191953348⟩]
theorem checked64309 : checkPrefixCuts (2^48) 8433041409 10 Manual.Count131072.C064309.packed 64 cuts64309 = true := by
 decide +kernel
def pointBounds64309 : List (Nat × Nat × Nat) := [(8433090560,114771970442635,114772359340693)]
theorem point_links_checked64309 : (cuts64309.take 1).map (fun c => (8433041409-1+2*2^10*c.k,114771896444657+c.lower,114772285342673+c.upper)) = pointBounds64309 := by
 decide +kernel
def cuts64310 : List PrefixCut := [⟨64,193585705,193585821⟩]
theorem checked64310 : checkPrefixCuts (2^48) 8433172481 10 Manual.Count131072.C064310.packed 64 cuts64310 = true := by
 decide +kernel
def cuts64311 : List PrefixCut := [⟨25,73628528,73628569⟩,
⟨64,190011438,190011548⟩]
theorem checked64311 : checkPrefixCuts (2^48) 8433303553 10 Manual.Count131072.C064311.packed 64 cuts64311 = true := by
 decide +kernel
def pointBounds64311 : List (Nat × Nat × Nat) := [(8433354752,114772355612133,114772744510411)]
theorem point_links_checked64311 : (cuts64311.take 1).map (fun c => (8433303553-1+2*2^10*c.k,114772281983605+c.lower,114772670881842+c.upper)) = pointBounds64311 := by
 decide +kernel
def cuts64312 : List PrefixCut := [⟨64,190976390,190976497⟩]
theorem checked64312 : checkPrefixCuts (2^48) 8433434625 10 Manual.Count131072.C064312.packed 64 cuts64312 = true := by
 decide +kernel
def cuts64313 : List PrefixCut := [⟨26,78232044,78232090⟩,
⟨64,193242936,193243045⟩]
theorem checked64313 : checkPrefixCuts (2^48) 8433565697 10 Manual.Count131072.C064313.packed 64 cuts64313 = true := by
 decide +kernel
def pointBounds64313 : List (Nat × Nat × Nat) := [(8433618944,114772741203477,114773130101977)]
theorem point_links_checked64313 : (cuts64313.take 1).map (fun c => (8433565697-1+2*2^10*c.k,114772662971433+c.lower,114773051869887+c.upper)) = pointBounds64313 := by
 decide +kernel
def cuts64314 : List PrefixCut := [⟨64,193406804,193406917⟩]
theorem checked64314 : checkPrefixCuts (2^48) 8433696769 10 Manual.Count131072.C064314.packed 64 cuts64314 = true := by
 decide +kernel
def cuts64315 : List PrefixCut := [⟨27,79397706,79397754⟩,
⟨64,189799371,189799482⟩]
theorem checked64315 : checkPrefixCuts (2^48) 8433827841 10 Manual.Count131072.C064315.packed 64 cuts64315 = true := by
 decide +kernel
def pointBounds64315 : List (Nat × Nat × Nat) := [(8433883136,114773129018879,114773517917603)]
theorem point_links_checked64315 : (cuts64315.take 1).map (fun c => (8433827841-1+2*2^10*c.k,114773049621173+c.lower,114773438519849+c.upper)) = pointBounds64315 := by
 decide +kernel
def cuts64316 : List PrefixCut := [⟨64,192032474,192032585⟩]
theorem checked64316 : checkPrefixCuts (2^48) 8433958913 10 Manual.Count131072.C064316.packed 64 cuts64316 = true := by
 decide +kernel
def cuts64317 : List PrefixCut := [⟨28,82432201,82432248⟩,
⟨64,190527680,190527791⟩]
theorem checked64317 : checkPrefixCuts (2^48) 8434089985 10 Manual.Count131072.C064317.packed 64 cuts64317 = true := by
 decide +kernel
def pointBounds64317 : List (Nat × Nat × Nat) := [(8434147328,114773513885219,114773902784164)]
theorem point_links_checked64317 : (cuts64317.take 1).map (fun c => (8434089985-1+2*2^10*c.k,114773431453018+c.lower,114773820351916+c.upper)) = pointBounds64317 := by
 decide +kernel
def cuts64318 : List PrefixCut := [⟨64,192660589,192660701⟩]
theorem checked64318 : checkPrefixCuts (2^48) 8434221057 10 Manual.Count131072.C064318.packed 64 cuts64318 = true := by
 decide +kernel
def cuts64319 : List PrefixCut := [⟨29,85833610,85833660⟩,
⟨64,188619560,188619669⟩]
theorem checked64319 : checkPrefixCuts (2^48) 8434352129 10 Manual.Count131072.C064319.packed 64 cuts64319 = true := by
 decide +kernel
def pointBounds64319 : List (Nat × Nat × Nat) := [(8434411520,114773900474897,114774289374068)]
theorem point_links_checked64319 : (cuts64319.take 1).map (fun c => (8434352129-1+2*2^10*c.k,114773814641287+c.lower,114774203540408+c.upper)) = pointBounds64319 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000134
