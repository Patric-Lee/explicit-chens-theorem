import PlattAssemblyKernel
import PlattCertificates.Count131072.C062304
import PlattCertificates.Count131072.C062305
import PlattCertificates.Count131072.C062306
import PlattCertificates.Count131072.C062307
import PlattCertificates.Count131072.C062308
import PlattCertificates.Count131072.C062309
import PlattCertificates.Count131072.C062310
import PlattCertificates.Count131072.C062311
import PlattCertificates.Count131072.C062312
import PlattCertificates.Count131072.C062313
import PlattCertificates.Count131072.C062314
import PlattCertificates.Count131072.C062315
import PlattCertificates.Count131072.C062316
import PlattCertificates.Count131072.C062317
import PlattCertificates.Count131072.C062318
import PlattCertificates.Count131072.C062319
import PlattCertificates.Count131072.C062320
import PlattCertificates.Count131072.C062321
import PlattCertificates.Count131072.C062322
import PlattCertificates.Count131072.C062323
import PlattCertificates.Count131072.C062324
import PlattCertificates.Count131072.C062325
import PlattCertificates.Count131072.C062326
import PlattCertificates.Count131072.C062327
import PlattCertificates.Count131072.C062328
import PlattCertificates.Count131072.C062329
import PlattCertificates.Count131072.C062330
import PlattCertificates.Count131072.C062331
import PlattCertificates.Count131072.C062332
import PlattCertificates.Count131072.C062333
import PlattCertificates.Count131072.C062334
import PlattCertificates.Count131072.C062335
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62304 : List PrefixCut := [⟨39,121991211,121991276⟩,
⟨64,197059476,197059581⟩]
theorem checked62304 : checkPrefixCuts (2^48) 8170242049 10 Manual.Count131072.C062304.packed 64 cuts62304 = true := by
 decide +kernel
def pointBounds62304 : List (Nat × Nat × Nat) := [(8170321920,114381803516482,114382192190004)]
theorem point_links_checked62304 : (cuts62304.take 1).map (fun c => (8170242049-1+2*2^10*c.k,114381681525271+c.lower,114382070198728+c.upper)) = pointBounds62304 := by
 decide +kernel
def cuts62305 : List PrefixCut := [⟨64,197814210,197814328⟩]
theorem checked62305 : checkPrefixCuts (2^48) 8170373121 10 Manual.Count131072.C062305.packed 64 cuts62305 = true := by
 decide +kernel
def cuts62306 : List PrefixCut := [⟨36,111307853,111307915⟩,
⟨64,197053142,197053257⟩]
theorem checked62306 : checkPrefixCuts (2^48) 8170504193 10 Manual.Count131072.C062306.packed 64 cuts62306 = true := by
 decide +kernel
def pointBounds62306 : List (Nat × Nat × Nat) := [(8170577920,114382187706810,114382576380552)]
theorem point_links_checked62306 : (cuts62306.take 1).map (fun c => (8170504193-1+2*2^10*c.k,114382076398957+c.lower,114382465072637+c.upper)) = pointBounds62306 := by
 decide +kernel
def cuts62307 : List PrefixCut := [⟨64,201218339,201218451⟩]
theorem checked62307 : checkPrefixCuts (2^48) 8170635265 10 Manual.Count131072.C062307.packed 64 cuts62307 = true := by
 decide +kernel
def cuts62308 : List PrefixCut := [⟨33,99970643,99970702⟩,
⟨64,197081250,197081363⟩]
theorem checked62308 : checkPrefixCuts (2^48) 8170766337 10 Manual.Count131072.C062308.packed 64 cuts62308 = true := by
 decide +kernel
def pointBounds62308 : List (Nat × Nat × Nat) := [(8170833920,114382574641081,114382963315047)]
theorem point_links_checked62308 : (cuts62308.take 1).map (fun c => (8170766337-1+2*2^10*c.k,114382474670438+c.lower,114382863344345+c.upper)) = pointBounds62308 := by
 decide +kernel
def cuts62309 : List PrefixCut := [⟨64,196079120,196079233⟩]
theorem checked62309 : checkPrefixCuts (2^48) 8170897409 10 Manual.Count131072.C062309.packed 64 cuts62309 = true := by
 decide +kernel
def cuts62310 : List PrefixCut := [⟨30,92630096,92630147⟩,
⟨64,198521737,198521850⟩]
theorem checked62310 : checkPrefixCuts (2^48) 8171028481 10 Manual.Count131072.C062310.packed 64 cuts62310 = true := by
 decide +kernel
def pointBounds62310 : List (Nat × Nat × Nat) := [(8171089920,114382960460904,114383349135088)]
theorem point_links_checked62310 : (cuts62310.take 1).map (fun c => (8171028481-1+2*2^10*c.k,114382867830808+c.lower,114383256504941+c.upper)) = pointBounds62310 := by
 decide +kernel
def cuts62311 : List PrefixCut := [⟨64,197726278,197726389⟩]
theorem checked62311 : checkPrefixCuts (2^48) 8171159553 10 Manual.Count131072.C062311.packed 64 cuts62311 = true := by
 decide +kernel
def cuts62312 : List PrefixCut := [⟨27,84669978,84670023⟩,
⟨64,198446493,198446601⟩]
theorem checked62312 : checkPrefixCuts (2^48) 8171290625 10 Manual.Count131072.C062312.packed 64 cuts62312 = true := by
 decide +kernel
def pointBounds62312 : List (Nat × Nat × Nat) := [(8171345920,114383348748801,114383737423203)]
theorem point_links_checked62312 : (cuts62312.take 1).map (fun c => (8171290625-1+2*2^10*c.k,114383264078823+c.lower,114383652753180+c.upper)) = pointBounds62312 := by
 decide +kernel
def cuts62313 : List PrefixCut := [⟨64,198064395,198064511⟩]
theorem checked62313 : checkPrefixCuts (2^48) 8171421697 10 Manual.Count131072.C062313.packed 64 cuts62313 = true := by
 decide +kernel
def cuts62314 : List PrefixCut := [⟨24,74333610,74333652⟩,
⟨64,196132276,196132388⟩]
theorem checked62314 : checkPrefixCuts (2^48) 8171552769 10 Manual.Count131072.C062314.packed 64 cuts62314 = true := by
 decide +kernel
def pointBounds62314 : List (Nat × Nat × Nat) := [(8171601920,114383734923321,114384123597944)]
theorem point_links_checked62314 : (cuts62314.take 1).map (fun c => (8171552769-1+2*2^10*c.k,114383660589711+c.lower,114384049264292+c.upper)) = pointBounds62314 := by
 decide +kernel
def cuts62315 : List PrefixCut := [⟨64,199539166,199539284⟩]
theorem checked62315 : checkPrefixCuts (2^48) 8171683841 10 Manual.Count131072.C062315.packed 64 cuts62315 = true := by
 decide +kernel
def cuts62316 : List PrefixCut := [⟨21,66236791,66236831⟩,
⟨64,197985982,197986095⟩]
theorem checked62316 : checkPrefixCuts (2^48) 8171814913 10 Manual.Count131072.C062316.packed 64 cuts62316 = true := by
 decide +kernel
def pointBounds62316 : List (Nat × Nat × Nat) := [(8171857920,114384122497944,114384511172795)]
theorem point_links_checked62316 : (cuts62316.take 1).map (fun c => (8171814913-1+2*2^10*c.k,114384056261153+c.lower,114384444935964+c.upper)) = pointBounds62316 := by
 decide +kernel
def cuts62317 : List PrefixCut := [⟨64,195881735,195881852⟩]
theorem checked62317 : checkPrefixCuts (2^48) 8171945985 10 Manual.Count131072.C062317.packed 64 cuts62317 = true := by
 decide +kernel
def cuts62318 : List PrefixCut := [⟨18,55763893,55763927⟩,
⟨64,197394099,197394211⟩]
theorem checked62318 : checkPrefixCuts (2^48) 8172077057 10 Manual.Count131072.C062318.packed 64 cuts62318 = true := by
 decide +kernel
def pointBounds62318 : List (Nat × Nat × Nat) := [(8172113920,114384505892763,114384894567838)]
theorem point_links_checked62318 : (cuts62318.take 1).map (fun c => (8172077057-1+2*2^10*c.k,114384450128870+c.lower,114384838803911+c.upper)) = pointBounds62318 := by
 decide +kernel
def cuts62319 : List PrefixCut := [⟨64,199216388,199216505⟩]
theorem checked62319 : checkPrefixCuts (2^48) 8172208129 10 Manual.Count131072.C062319.packed 64 cuts62319 = true := by
 decide +kernel
def cuts62320 : List PrefixCut := [⟨15,46841563,46841587⟩,
⟨64,197181112,197181223⟩]
theorem checked62320 : checkPrefixCuts (2^48) 8172339201 10 Manual.Count131072.C062320.packed 64 cuts62320 = true := by
 decide +kernel
def pointBounds62320 : List (Nat × Nat × Nat) := [(8172369920,114384893580920,114385282256214)]
theorem point_links_checked62320 : (cuts62320.take 1).map (fun c => (8172339201-1+2*2^10*c.k,114384846739357+c.lower,114385235414627+c.upper)) = pointBounds62320 := by
 decide +kernel
def cuts62321 : List PrefixCut := [⟨64,199313315,199313432⟩]
theorem checked62321 : checkPrefixCuts (2^48) 8172470273 10 Manual.Count131072.C062321.packed 64 cuts62321 = true := by
 decide +kernel
def cuts62322 : List PrefixCut := [⟨12,37265415,37265436⟩,
⟨64,194832792,194832904⟩]
theorem checked62322 : checkPrefixCuts (2^48) 8172601345 10 Manual.Count131072.C062322.packed 64 cuts62322 = true := by
 decide +kernel
def pointBounds62322 : List (Nat × Nat × Nat) := [(8172625920,114385280499199,114385669174718)]
theorem point_links_checked62322 : (cuts62322.take 1).map (fun c => (8172601345-1+2*2^10*c.k,114385243233784+c.lower,114385631909282+c.upper)) = pointBounds62322 := by
 decide +kernel
def cuts62323 : List PrefixCut := [⟨64,198308153,198308272⟩]
theorem checked62323 : checkPrefixCuts (2^48) 8172732417 10 Manual.Count131072.C062323.packed 64 cuts62323 = true := by
 decide +kernel
def cuts62324 : List PrefixCut := [⟨9,27311035,27311049⟩,
⟨64,197926133,197926246⟩]
theorem checked62324 : checkPrefixCuts (2^48) 8172863489 10 Manual.Count131072.C062324.packed 64 cuts62324 = true := by
 decide +kernel
def pointBounds62324 : List (Nat × Nat × Nat) := [(8172881920,114385663685764,114386052361507)]
theorem point_links_checked62324 : (cuts62324.take 1).map (fun c => (8172863489-1+2*2^10*c.k,114385636374729+c.lower,114386025050458+c.upper)) = pointBounds62324 := by
 decide +kernel
def cuts62325 : List PrefixCut := [⟨64,197234186,197234289⟩]
theorem checked62325 : checkPrefixCuts (2^48) 8172994561 10 Manual.Count131072.C062325.packed 64 cuts62325 = true := by
 decide +kernel
def cuts62326 : List PrefixCut := [⟨6,17908307,17908317⟩,
⟨64,199262888,199262997⟩]
theorem checked62326 : checkPrefixCuts (2^48) 8173125633 10 Manual.Count131072.C062326.packed 64 cuts62326 = true := by
 decide +kernel
def pointBounds62326 : List (Nat × Nat × Nat) := [(8173137920,114386049443355,114386438119310)]
theorem point_links_checked62326 : (cuts62326.take 1).map (fun c => (8173125633-1+2*2^10*c.k,114386031535048+c.lower,114386420210993+c.upper)) = pointBounds62326 := by
 decide +kernel
def cuts62327 : List PrefixCut := [⟨64,200258398,200258516⟩]
theorem checked62327 : checkPrefixCuts (2^48) 8173256705 10 Manual.Count131072.C062327.packed 64 cuts62327 = true := by
 decide +kernel
def cuts62328 : List PrefixCut := [⟨3,9194935,9194940⟩,
⟨64,194917359,194917472⟩]
theorem checked62328 : checkPrefixCuts (2^48) 8173387777 10 Manual.Count131072.C062328.packed 64 cuts62328 = true := by
 decide +kernel
def pointBounds62328 : List (Nat × Nat × Nat) := [(8173393920,114386440251269,114386828927446)]
theorem point_links_checked62328 : (cuts62328.take 1).map (fun c => (8173387777-1+2*2^10*c.k,114386431056334+c.lower,114386819732506+c.upper)) = pointBounds62328 := by
 decide +kernel
def cuts62329 : List PrefixCut := [⟨64,197910253,197910369⟩]
theorem checked62329 : checkPrefixCuts (2^48) 8173518849 10 Manual.Count131072.C062329.packed 64 cuts62329 = true := by
 decide +kernel
def pointBounds62329 : List (Nat × Nat × Nat) := [(8173649920,114386823883946,114387212560347)]
theorem point_links_checked62329 : (cuts62329.take 1).map (fun c => (8173518849-1+2*2^10*c.k,114386625973693+c.lower,114387014649978+c.upper)) = pointBounds62329 := by
 decide +kernel
def cuts62330 : List PrefixCut := [⟨64,197011761,197011875⟩]
theorem checked62330 : checkPrefixCuts (2^48) 8173649921 10 Manual.Count131072.C062330.packed 64 cuts62330 = true := by
 decide +kernel
def cuts62331 : List PrefixCut := [⟨61,187332120,187332227⟩,
⟨64,197421802,197421915⟩]
theorem checked62331 : checkPrefixCuts (2^48) 8173780993 10 Manual.Count131072.C062331.packed 64 cuts62331 = true := by
 decide +kernel
def pointBounds62331 : List (Nat × Nat × Nat) := [(8173905920,114387208227827,114387596904449)]
theorem point_links_checked62331 : (cuts62331.take 1).map (fun c => (8173780993-1+2*2^10*c.k,114387020895707+c.lower,114387409572222+c.upper)) = pointBounds62331 := by
 decide +kernel
def cuts62332 : List PrefixCut := [⟨64,196626617,196626728⟩]
theorem checked62332 : checkPrefixCuts (2^48) 8173912065 10 Manual.Count131072.C062332.packed 64 cuts62332 = true := by
 decide +kernel
def cuts62333 : List PrefixCut := [⟨58,178476401,178476500⟩,
⟨64,196967826,196967936⟩]
theorem checked62333 : checkPrefixCuts (2^48) 8174043137 10 Manual.Count131072.C062333.packed 64 cuts62333 = true := by
 decide +kernel
def pointBounds62333 : List (Nat × Nat × Nat) := [(8174161920,114387593420527,114387982097365)]
theorem point_links_checked62333 : (cuts62333.take 1).map (fun c => (8174043137-1+2*2^10*c.k,114387414944126+c.lower,114387803620865+c.upper)) = pointBounds62333 := by
 decide +kernel
def cuts62334 : List PrefixCut := [⟨64,196413713,196413826⟩]
theorem checked62334 : checkPrefixCuts (2^48) 8174174209 10 Manual.Count131072.C062334.packed 64 cuts62334 = true := by
 decide +kernel
def cuts62335 : List PrefixCut := [⟨55,170378792,170378884⟩,
⟨64,197719064,197719173⟩]
theorem checked62335 : checkPrefixCuts (2^48) 8174305281 10 Manual.Count131072.C062335.packed 64 cuts62335 = true := by
 decide +kernel
def pointBounds62335 : List (Nat × Nat × Nat) := [(8174417920,114387978704457,114388367381511)]
theorem point_links_checked62335 : (cuts62335.take 1).map (fun c => (8174305281-1+2*2^10*c.k,114387808325665+c.lower,114388197002627+c.upper)) = pointBounds62335 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000072
