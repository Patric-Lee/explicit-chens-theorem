import PlattAssemblyKernel
import PlattCertificates.Count131072.C050320
import PlattCertificates.Count131072.C050321
import PlattCertificates.Count131072.C050322
import PlattCertificates.Count131072.C050323
import PlattCertificates.Count131072.C050324
import PlattCertificates.Count131072.C050325
import PlattCertificates.Count131072.C050326
import PlattCertificates.Count131072.C050327
import PlattCertificates.Count131072.C050328
import PlattCertificates.Count131072.C050329
import PlattCertificates.Count131072.C050330
import PlattCertificates.Count131072.C050331
import PlattCertificates.Count131072.C050332
import PlattCertificates.Count131072.C050333
import PlattCertificates.Count131072.C050334
import PlattCertificates.Count131072.C050335
import PlattCertificates.Count131072.C050336
import PlattCertificates.Count131072.C050337
import PlattCertificates.Count131072.C050338
import PlattCertificates.Count131072.C050339
import PlattCertificates.Count131072.C050340
import PlattCertificates.Count131072.C050341
import PlattCertificates.Count131072.C050342
import PlattCertificates.Count131072.C050343
import PlattCertificates.Count131072.C050344
import PlattCertificates.Count131072.C050345
import PlattCertificates.Count131072.C050346
import PlattCertificates.Count131072.C050347
import PlattCertificates.Count131072.C050348
import PlattCertificates.Count131072.C050349
import PlattCertificates.Count131072.C050350
import PlattCertificates.Count131072.C050351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50320 : List PrefixCut := [⟨35,137037255,137037332⟩,
⟨64,249549135,249549272⟩]
theorem checked50320 : checkPrefixCuts (2^48) 6599475201 10 Manual.Count131072.C050320.packed 64 cuts50320 = true := by
 decide +kernel
def pointBounds50320 : List (Nat × Nat × Nat) := [(6599546880,111736399176551,111736786343867)]
theorem point_links_checked50320 : (cuts50320.take 1).map (fun c => (6599475201-1+2*2^10*c.k,111736262139296+c.lower,111736649306535+c.upper)) = pointBounds50320 := by
 decide +kernel
def cuts50321 : List PrefixCut := [⟨64,246771936,246772079⟩]
theorem checked50321 : checkPrefixCuts (2^48) 6599606273 10 Manual.Count131072.C050321.packed 64 cuts50321 = true := by
 decide +kernel
def cuts50322 : List PrefixCut := [⟨8,30494289,30494308⟩,
⟨64,251117212,251117353⟩]
theorem checked50322 : checkPrefixCuts (2^48) 6599737345 10 Manual.Count131072.C050322.packed 64 cuts50322 = true := by
 decide +kernel
def pointBounds50322 : List (Nat × Nat × Nat) := [(6599753728,111736788954656,111737176122194)]
theorem point_links_checked50322 : (cuts50322.take 1).map (fun c => (6599737345-1+2*2^10*c.k,111736758460367+c.lower,111737145627886+c.upper)) = pointBounds50322 := by
 decide +kernel
def cuts50323 : List PrefixCut := [⟨45,174772595,174772694⟩,
⟨64,251026928,251027071⟩]
theorem checked50323 : checkPrefixCuts (2^48) 6599868417 10 Manual.Count131072.C050323.packed 64 cuts50323 = true := by
 decide +kernel
def pointBounds50323 : List (Nat × Nat × Nat) := [(6599960576,111737184350174,111737571517933)]
theorem point_links_checked50323 : (cuts50323.take 1).map (fun c => (6599868417-1+2*2^10*c.k,111737009577579+c.lower,111737396745239+c.upper)) = pointBounds50323 := by
 decide +kernel
def cuts50324 : List PrefixCut := [⟨64,248420485,248420626⟩]
theorem checked50324 : checkPrefixCuts (2^48) 6599999489 10 Manual.Count131072.C050324.packed 64 cuts50324 = true := by
 decide +kernel
def cuts50325 : List PrefixCut := [⟨18,68789207,68789245⟩,
⟨64,248543468,248543607⟩]
theorem checked50325 : checkPrefixCuts (2^48) 6600130561 10 Manual.Count131072.C050325.packed 64 cuts50325 = true := by
 decide +kernel
def pointBounds50325 : List (Nat × Nat × Nat) := [(6600167424,111737577814199,111737964982181)]
theorem point_links_checked50325 : (cuts50325.take 1).map (fun c => (6600130561-1+2*2^10*c.k,111737509024992+c.lower,111737896192936+c.upper)) = pointBounds50325 := by
 decide +kernel
def cuts50326 : List PrefixCut := [⟨55,213057685,213057808⟩,
⟨64,247770906,247771048⟩]
theorem checked50326 : checkPrefixCuts (2^48) 6600261633 10 Manual.Count131072.C050326.packed 64 cuts50326 = true := by
 decide +kernel
def pointBounds50326 : List (Nat × Nat × Nat) := [(6600374272,111737970626145,111738357794351)]
theorem point_links_checked50326 : (cuts50326.take 1).map (fun c => (6600261633-1+2*2^10*c.k,111737757568460+c.lower,111738144736543+c.upper)) = pointBounds50326 := by
 decide +kernel
def cuts50327 : List PrefixCut := [⟨64,249514444,249514581⟩]
theorem checked50327 : checkPrefixCuts (2^48) 6600392705 10 Manual.Count131072.C050327.packed 64 cuts50327 = true := by
 decide +kernel
def cuts50328 : List PrefixCut := [⟨28,108230830,108230892⟩,
⟨64,246652341,246652480⟩]
theorem checked50328 : checkPrefixCuts (2^48) 6600523777 10 Manual.Count131072.C050328.packed 64 cuts50328 = true := by
 decide +kernel
def pointBounds50328 : List (Nat × Nat × Nat) := [(6600581120,111738363084640,111738750253064)]
theorem point_links_checked50328 : (cuts50328.take 1).map (fun c => (6600523777-1+2*2^10*c.k,111738254853810+c.lower,111738642022172+c.upper)) = pointBounds50328 := by
 decide +kernel
def cuts50329 : List PrefixCut := [⟨64,247926730,247926872⟩]
theorem checked50329 : checkPrefixCuts (2^48) 6600654849 10 Manual.Count131072.C050329.packed 64 cuts50329 = true := by
 decide +kernel
def cuts50330 : List PrefixCut := [⟨1,3795194,3795196⟩,
⟨64,248177672,248177809⟩]
theorem checked50330 : checkPrefixCuts (2^48) 6600785921 10 Manual.Count131072.C050330.packed 64 cuts50330 = true := by
 decide +kernel
def pointBounds50330 : List (Nat × Nat × Nat) := [(6600787968,111738753228075,111739140396720)]
theorem point_links_checked50330 : (cuts50330.take 1).map (fun c => (6600785921-1+2*2^10*c.k,111738749432881+c.lower,111739136601524+c.upper)) = pointBounds50330 := by
 decide +kernel
def cuts50331 : List PrefixCut := [⟨38,144853298,144853382⟩,
⟨64,247106680,247106820⟩]
theorem checked50331 : checkPrefixCuts (2^48) 6600916993 10 Manual.Count131072.C050331.packed 64 cuts50331 = true := by
 decide +kernel
def pointBounds50331 : List (Nat × Nat × Nat) := [(6600994816,111739142463851,111739529632715)]
theorem point_links_checked50331 : (cuts50331.take 1).map (fun c => (6600916993-1+2*2^10*c.k,111738997610553+c.lower,111739384779333+c.upper)) = pointBounds50331 := by
 decide +kernel
def cuts50332 : List PrefixCut := [⟨64,246163715,246163854⟩]
theorem checked50332 : checkPrefixCuts (2^48) 6601048065 10 Manual.Count131072.C050332.packed 64 cuts50332 = true := by
 decide +kernel
def cuts50333 : List PrefixCut := [⟨11,44175063,44175086⟩,
⟨64,247821770,247821908⟩]
theorem checked50333 : checkPrefixCuts (2^48) 6601179137 10 Manual.Count131072.C050333.packed 64 cuts50333 = true := by
 decide +kernel
def pointBounds50333 : List (Nat × Nat × Nat) := [(6601201664,111739535056011,111739922225093)]
theorem point_links_checked50333 : (cuts50333.take 1).map (fun c => (6601179137-1+2*2^10*c.k,111739490880948+c.lower,111739878050007+c.upper)) = pointBounds50333 := by
 decide +kernel
def cuts50334 : List PrefixCut := [⟨48,185564622,185564727⟩,
⟨64,246921431,246921571⟩]
theorem checked50334 : checkPrefixCuts (2^48) 6601310209 10 Manual.Count131072.C050334.packed 64 cuts50334 = true := by
 decide +kernel
def pointBounds50334 : List (Nat × Nat × Nat) := [(6601408512,111739924267340,111740311436642)]
theorem point_links_checked50334 : (cuts50334.take 1).map (fun c => (6601310209-1+2*2^10*c.k,111739738702718+c.lower,111740125871915+c.upper)) = pointBounds50334 := by
 decide +kernel
def cuts50335 : List PrefixCut := [⟨64,247769300,247769440⟩]
theorem checked50335 : checkPrefixCuts (2^48) 6601441281 10 Manual.Count131072.C050335.packed 64 cuts50335 = true := by
 decide +kernel
def cuts50336 : List PrefixCut := [⟨21,80414160,80414208⟩,
⟨64,247508539,247508679⟩]
theorem checked50336 : checkPrefixCuts (2^48) 6601572353 10 Manual.Count131072.C050336.packed 64 cuts50336 = true := by
 decide +kernel
def pointBounds50336 : List (Nat × Nat × Nat) := [(6601615360,111740313807609,111740700977134)]
theorem point_links_checked50336 : (cuts50336.take 1).map (fun c => (6601572353-1+2*2^10*c.k,111740233393449+c.lower,111740620562926+c.upper)) = pointBounds50336 := by
 decide +kernel
def cuts50337 : List PrefixCut := [⟨58,221922059,221922187⟩,
⟨64,245201261,245201402⟩]
theorem checked50337 : checkPrefixCuts (2^48) 6601703425 10 Manual.Count131072.C050337.packed 64 cuts50337 = true := by
 decide +kernel
def pointBounds50337 : List (Nat × Nat × Nat) := [(6601822208,111740702824047,111741089993792)]
theorem point_links_checked50337 : (cuts50337.take 1).map (fun c => (6601703425-1+2*2^10*c.k,111740480901988+c.lower,111740868071605+c.upper)) = pointBounds50337 := by
 decide +kernel
def cuts50338 : List PrefixCut := [⟨64,247413432,247413578⟩]
theorem checked50338 : checkPrefixCuts (2^48) 6601834497 10 Manual.Count131072.C050338.packed 64 cuts50338 = true := by
 decide +kernel
def cuts50339 : List PrefixCut := [⟨31,120230161,120230231⟩,
⟨64,246385309,246385448⟩]
theorem checked50339 : checkPrefixCuts (2^48) 6601965569 10 Manual.Count131072.C050339.packed 64 cuts50339 = true := by
 decide +kernel
def pointBounds50339 : List (Nat × Nat × Nat) := [(6602029056,111741093746842,111741480916816)]
theorem point_links_checked50339 : (cuts50339.take 1).map (fun c => (6601965569-1+2*2^10*c.k,111740973516681+c.lower,111741360686585+c.upper)) = pointBounds50339 := by
 decide +kernel
def cuts50340 : List PrefixCut := [⟨64,247659413,247659551⟩]
theorem checked50340 : checkPrefixCuts (2^48) 6602096641 10 Manual.Count131072.C050340.packed 64 cuts50340 = true := by
 decide +kernel
def cuts50341 : List PrefixCut := [⟨4,15731686,15731695⟩,
⟨64,246247616,246247754⟩]
theorem checked50341 : checkPrefixCuts (2^48) 6602227713 10 Manual.Count131072.C050341.packed 64 cuts50341 = true := by
 decide +kernel
def pointBounds50341 : List (Nat × Nat × Nat) := [(6602235904,111741483293089,111741870463279)]
theorem point_links_checked50341 : (cuts50341.take 1).map (fun c => (6602227713-1+2*2^10*c.k,111741467561403+c.lower,111741854731584+c.upper)) = pointBounds50341 := by
 decide +kernel
def cuts50342 : List PrefixCut := [⟨41,160893930,160894019⟩,
⟨64,250505935,250506074⟩]
theorem checked50342 : checkPrefixCuts (2^48) 6602358785 10 Manual.Count131072.C050342.packed 64 cuts50342 = true := by
 decide +kernel
def pointBounds50342 : List (Nat × Nat × Nat) := [(6602442752,111741874702949,111742261873357)]
theorem point_links_checked50342 : (cuts50342.take 1).map (fun c => (6602358785-1+2*2^10*c.k,111741713809019+c.lower,111742100979338+c.upper)) = pointBounds50342 := by
 decide +kernel
def cuts50343 : List PrefixCut := [⟨64,245470467,245470605⟩]
theorem checked50343 : checkPrefixCuts (2^48) 6602489857 10 Manual.Count131072.C050343.packed 64 cuts50343 = true := by
 decide +kernel
def cuts50344 : List PrefixCut := [⟨14,54268872,54268902⟩,
⟨64,246701901,246702039⟩]
theorem checked50344 : checkPrefixCuts (2^48) 6602620929 10 Manual.Count131072.C050344.packed 64 cuts50344 = true := by
 decide +kernel
def pointBounds50344 : List (Nat × Nat × Nat) := [(6602649600,111742264054293,111742651224919)]
theorem point_links_checked50344 : (cuts50344.take 1).map (fun c => (6602620929-1+2*2^10*c.k,111742209785421+c.lower,111742596956017+c.upper)) = pointBounds50344 := by
 decide +kernel
def cuts50345 : List PrefixCut := [⟨51,195115667,195115779⟩,
⟨64,245972272,245972414⟩]
theorem checked50345 : checkPrefixCuts (2^48) 6602752001 10 Manual.Count131072.C050345.packed 64 cuts50345 = true := by
 decide +kernel
def pointBounds50345 : List (Nat × Nat × Nat) := [(6602856448,111742651602989,111743038773835)]
theorem point_links_checked50345 : (cuts50345.take 1).map (fun c => (6602752001-1+2*2^10*c.k,111742456487322+c.lower,111742843658056+c.upper)) = pointBounds50345 := by
 decide +kernel
def cuts50346 : List PrefixCut := [⟨64,246137921,246138065⟩]
theorem checked50346 : checkPrefixCuts (2^48) 6602883073 10 Manual.Count131072.C050346.packed 64 cuts50346 = true := by
 decide +kernel
def cuts50347 : List PrefixCut := [⟨24,90755191,90755243⟩,
⟨64,243745868,243746012⟩]
theorem checked50347 : checkPrefixCuts (2^48) 6603014145 10 Manual.Count131072.C050347.packed 64 cuts50347 = true := by
 decide +kernel
def pointBounds50347 : List (Nat × Nat × Nat) := [(6603063296,111743039352706,111743426523778)]
theorem point_links_checked50347 : (cuts50347.take 1).map (fun c => (6603014145-1+2*2^10*c.k,111742948597515+c.lower,111743335768535+c.upper)) = pointBounds50347 := by
 decide +kernel
def cuts50348 : List PrefixCut := [⟨61,232231864,232231992⟩,
⟨64,243783666,243783800⟩]
theorem checked50348 : checkPrefixCuts (2^48) 6603145217 10 Manual.Count131072.C050348.packed 64 cuts50348 = true := by
 decide +kernel
def pointBounds50348 : List (Nat × Nat × Nat) := [(6603270144,111743424575247,111743811746539)]
theorem point_links_checked50348 : (cuts50348.take 1).map (fun c => (6603145217-1+2*2^10*c.k,111743192343383+c.lower,111743579514547+c.upper)) = pointBounds50348 := by
 decide +kernel
def cuts50349 : List PrefixCut := [⟨64,247657782,247657926⟩]
theorem checked50349 : checkPrefixCuts (2^48) 6603276289 10 Manual.Count131072.C050349.packed 64 cuts50349 = true := by
 decide +kernel
def cuts50350 : List PrefixCut := [⟨34,131925868,131925945⟩,
⟨64,246161021,246161163⟩]
theorem checked50350 : checkPrefixCuts (2^48) 6603407361 10 Manual.Count131072.C050350.packed 64 cuts50350 = true := by
 decide +kernel
def pointBounds50350 : List (Nat × Nat × Nat) := [(6603476992,111743815710699,111744202882218)]
theorem point_links_checked50350 : (cuts50350.take 1).map (fun c => (6603407361-1+2*2^10*c.k,111743683784831+c.lower,111744070956273+c.upper)) = pointBounds50350 := by
 decide +kernel
def cuts50351 : List PrefixCut := [⟨64,249097202,249097345⟩]
theorem checked50351 : checkPrefixCuts (2^48) 6603538433 10 Manual.Count131072.C050351.packed 64 cuts50351 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000010
