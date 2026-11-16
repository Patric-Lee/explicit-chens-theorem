import PlattAssemblyKernel
import PlattCertificates.Count131072.C055280
import PlattCertificates.Count131072.C055281
import PlattCertificates.Count131072.C055282
import PlattCertificates.Count131072.C055283
import PlattCertificates.Count131072.C055284
import PlattCertificates.Count131072.C055285
import PlattCertificates.Count131072.C055286
import PlattCertificates.Count131072.C055287
import PlattCertificates.Count131072.C055288
import PlattCertificates.Count131072.C055289
import PlattCertificates.Count131072.C055290
import PlattCertificates.Count131072.C055291
import PlattCertificates.Count131072.C055292
import PlattCertificates.Count131072.C055293
import PlattCertificates.Count131072.C055294
import PlattCertificates.Count131072.C055295
import PlattCertificates.Count131072.C055296
import PlattCertificates.Count131072.C055297
import PlattCertificates.Count131072.C055298
import PlattCertificates.Count131072.C055299
import PlattCertificates.Count131072.C055300
import PlattCertificates.Count131072.C055301
import PlattCertificates.Count131072.C055302
import PlattCertificates.Count131072.C055303
import PlattCertificates.Count131072.C055304
import PlattCertificates.Count131072.C055305
import PlattCertificates.Count131072.C055306
import PlattCertificates.Count131072.C055307
import PlattCertificates.Count131072.C055308
import PlattCertificates.Count131072.C055309
import PlattCertificates.Count131072.C055310
import PlattCertificates.Count131072.C055311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55280 : List PrefixCut := [⟨64,224569319,224569445⟩]
theorem checked55280 : checkPrefixCuts (2^48) 7249592321 10 Manual.Count131072.C055280.packed 64 cuts55280 = true := by
 decide +kernel
def cuts55281 : List PrefixCut := [⟨38,135190028,135190100⟩,
⟨64,227671290,227671413⟩]
theorem checked55281 : checkPrefixCuts (2^48) 7249723393 10 Manual.Count131072.C055281.packed 64 cuts55281 = true := by
 decide +kernel
def pointBounds55281 : List (Nat × Nat × Nat) := [(7249801216,112903780434334,112904168264879)]
theorem point_links_checked55281 : (cuts55281.take 1).map (fun c => (7249723393-1+2*2^10*c.k,112903645244306+c.lower,112904033074779+c.upper)) = pointBounds55281 := by
 decide +kernel
def cuts55282 : List PrefixCut := [⟨64,222736441,222736569⟩]
theorem checked55282 : checkPrefixCuts (2^48) 7249854465 10 Manual.Count131072.C055282.packed 64 cuts55282 = true := by
 decide +kernel
def cuts55283 : List PrefixCut := [⟨21,71979857,71979898⟩,
⟨64,220907711,220907836⟩]
theorem checked55283 : checkPrefixCuts (2^48) 7249985537 10 Manual.Count131072.C055283.packed 64 cuts55283 = true := by
 decide +kernel
def pointBounds55283 : List (Nat × Nat × Nat) := [(7250028544,112904167631894,112904555462659)]
theorem point_links_checked55283 : (cuts55283.take 1).map (fun c => (7249985537-1+2*2^10*c.k,112904095652037+c.lower,112904483482761+c.upper)) = pointBounds55283 := by
 decide +kernel
def cuts55284 : List PrefixCut := [⟨64,226183674,226183801⟩]
theorem checked55284 : checkPrefixCuts (2^48) 7250116609 10 Manual.Count131072.C055284.packed 64 cuts55284 = true := by
 decide +kernel
def cuts55285 : List PrefixCut := [⟨4,14442073,14442080⟩,
⟨64,224238452,224238579⟩]
theorem checked55285 : checkPrefixCuts (2^48) 7250247681 10 Manual.Count131072.C055285.packed 64 cuts55285 = true := by
 decide +kernel
def pointBounds55285 : List (Nat × Nat × Nat) := [(7250255872,112904557185495,112904945016478)]
theorem point_links_checked55285 : (cuts55285.take 1).map (fun c => (7250247681-1+2*2^10*c.k,112904542743422+c.lower,112904930574398+c.upper)) = pointBounds55285 := by
 decide +kernel
def cuts55286 : List PrefixCut := [⟨51,178968580,178968682⟩,
⟨64,224661445,224661573⟩]
theorem checked55286 : checkPrefixCuts (2^48) 7250378753 10 Manual.Count131072.C055286.packed 64 cuts55286 = true := by
 decide +kernel
def pointBounds55286 : List (Nat × Nat × Nat) := [(7250483200,112904945950454,112905333781659)]
theorem point_links_checked55286 : (cuts55286.take 1).map (fun c => (7250378753-1+2*2^10*c.k,112904766981874+c.lower,112905154812977+c.upper)) = pointBounds55286 := by
 decide +kernel
def cuts55287 : List PrefixCut := [⟨64,224540909,224541037⟩]
theorem checked55287 : checkPrefixCuts (2^48) 7250509825 10 Manual.Count131072.C055287.packed 64 cuts55287 = true := by
 decide +kernel
def cuts55288 : List PrefixCut := [⟨34,118713099,118713168⟩,
⟨64,225584984,225585114⟩]
theorem checked55288 : checkPrefixCuts (2^48) 7250640897 10 Manual.Count131072.C055288.packed 64 cuts55288 = true := by
 decide +kernel
def pointBounds55288 : List (Nat × Nat × Nat) := [(7250710528,112905334897327,112905722728755)]
theorem point_links_checked55288 : (cuts55288.take 1).map (fun c => (7250640897-1+2*2^10*c.k,112905216184228+c.lower,112905604015587+c.upper)) = pointBounds55288 := by
 decide +kernel
def cuts55289 : List PrefixCut := [⟨64,225037450,225037578⟩]
theorem checked55289 : checkPrefixCuts (2^48) 7250771969 10 Manual.Count131072.C055289.packed 64 cuts55289 = true := by
 decide +kernel
def cuts55290 : List PrefixCut := [⟨17,60286209,60286243⟩,
⟨64,223441811,223441938⟩]
theorem checked55290 : checkPrefixCuts (2^48) 7250903041 10 Manual.Count131072.C055290.packed 64 cuts55290 = true := by
 decide +kernel
def pointBounds55290 : List (Nat × Nat × Nat) := [(7250937856,112905727092871,112906114924522)]
theorem point_links_checked55290 : (cuts55290.take 1).map (fun c => (7250903041-1+2*2^10*c.k,112905666806662+c.lower,112906054638279+c.upper)) = pointBounds55290 := by
 decide +kernel
def cuts55291 : List PrefixCut := [⟨64,225184571,225184694⟩]
theorem checked55291 : checkPrefixCuts (2^48) 7251034113 10 Manual.Count131072.C055291.packed 64 cuts55291 = true := by
 decide +kernel
def pointBounds55291 : List (Nat × Nat × Nat) := [(7251165184,112906115433044,112906503264911)]
theorem point_links_checked55291 : (cuts55291.take 1).map (fun c => (7251034113-1+2*2^10*c.k,112905890248473+c.lower,112906278080217+c.upper)) = pointBounds55291 := by
 decide +kernel
def cuts55292 : List PrefixCut := [⟨64,221027036,221027166⟩]
theorem checked55292 : checkPrefixCuts (2^48) 7251165185 10 Manual.Count131072.C055292.packed 64 cuts55292 = true := by
 decide +kernel
def cuts55293 : List PrefixCut := [⟨47,163729794,163729887⟩,
⟨64,222575722,222575850⟩]
theorem checked55293 : checkPrefixCuts (2^48) 7251296257 10 Manual.Count131072.C055293.packed 64 cuts55293 = true := by
 decide +kernel
def pointBounds55293 : List (Nat × Nat × Nat) := [(7251392512,112906500189874,112906888021964)]
theorem point_links_checked55293 : (cuts55293.take 1).map (fun c => (7251296257-1+2*2^10*c.k,112906336460080+c.lower,112906724292077+c.upper)) = pointBounds55293 := by
 decide +kernel
def cuts55294 : List PrefixCut := [⟨64,226414497,226414623⟩]
theorem checked55294 : checkPrefixCuts (2^48) 7251427329 10 Manual.Count131072.C055294.packed 64 cuts55294 = true := by
 decide +kernel
def cuts55295 : List PrefixCut := [⟨30,105423213,105423274⟩,
⟨64,224430811,224430940⟩]
theorem checked55295 : checkPrefixCuts (2^48) 7251558401 10 Manual.Count131072.C055295.packed 64 cuts55295 = true := by
 decide +kernel
def pointBounds55295 : List (Nat × Nat × Nat) := [(7251619840,112906890873512,112907278705824)]
theorem point_links_checked55295 : (cuts55295.take 1).map (fun c => (7251558401-1+2*2^10*c.k,112906785450299+c.lower,112907173282550+c.upper)) = pointBounds55295 := by
 decide +kernel
def cuts55296 : List PrefixCut := [⟨64,223107061,223107189⟩]
theorem checked55296 : checkPrefixCuts (2^48) 7251689473 10 Manual.Count131072.C055296.packed 64 cuts55296 = true := by
 decide +kernel
def cuts55297 : List PrefixCut := [⟨13,45567996,45568022⟩,
⟨64,225820013,225820142⟩]
theorem checked55297 : checkPrefixCuts (2^48) 7251820545 10 Manual.Count131072.C055297.packed 64 cuts55297 = true := by
 decide +kernel
def pointBounds55297 : List (Nat × Nat × Nat) := [(7251847168,112907278556167,112907666388701)]
theorem point_links_checked55297 : (cuts55297.take 1).map (fun c => (7251820545-1+2*2^10*c.k,112907232988171+c.lower,112907620820679+c.upper)) = pointBounds55297 := by
 decide +kernel
def cuts55298 : List PrefixCut := [⟨60,210601214,210601334⟩,
⟨64,224224575,224224703⟩]
theorem checked55298 : checkPrefixCuts (2^48) 7251951617 10 Manual.Count131072.C055298.packed 64 cuts55298 = true := by
 decide +kernel
def pointBounds55298 : List (Nat × Nat × Nat) := [(7252074496,112907669409398,112908057242155)]
theorem point_links_checked55298 : (cuts55298.take 1).map (fun c => (7251951617-1+2*2^10*c.k,112907458808184+c.lower,112907846640821+c.upper)) = pointBounds55298 := by
 decide +kernel
def cuts55299 : List PrefixCut := [⟨64,222396328,222396455⟩]
theorem checked55299 : checkPrefixCuts (2^48) 7252082689 10 Manual.Count131072.C055299.packed 64 cuts55299 = true := by
 decide +kernel
def cuts55300 : List PrefixCut := [⟨43,154821223,154821308⟩,
⟨64,227903629,227903754⟩]
theorem checked55300 : checkPrefixCuts (2^48) 7252213761 10 Manual.Count131072.C055300.packed 64 cuts55300 = true := by
 decide +kernel
def pointBounds55300 : List (Nat × Nat × Nat) := [(7252301824,112908060250310,112908448083287)]
theorem point_links_checked55300 : (cuts55300.take 1).map (fun c => (7252213761-1+2*2^10*c.k,112907905429087+c.lower,112908293261979+c.upper)) = pointBounds55300 := by
 decide +kernel
def cuts55301 : List PrefixCut := [⟨64,224522895,224523024⟩]
theorem checked55301 : checkPrefixCuts (2^48) 7252344833 10 Manual.Count131072.C055301.packed 64 cuts55301 = true := by
 decide +kernel
def cuts55302 : List PrefixCut := [⟨26,92175470,92175524⟩,
⟨64,221646874,221647004⟩]
theorem checked55302 : checkPrefixCuts (2^48) 7252475905 10 Manual.Count131072.C055302.packed 64 cuts55302 = true := by
 decide +kernel
def pointBounds55302 : List (Nat × Nat × Nat) := [(7252529152,112908450031081,112908837864281)]
theorem point_links_checked55302 : (cuts55302.take 1).map (fun c => (7252475905-1+2*2^10*c.k,112908357855611+c.lower,112908745688757+c.upper)) = pointBounds55302 := by
 decide +kernel
def cuts55303 : List PrefixCut := [⟨64,221099523,221099652⟩]
theorem checked55303 : checkPrefixCuts (2^48) 7252606977 10 Manual.Count131072.C055303.packed 64 cuts55303 = true := by
 decide +kernel
def cuts55304 : List PrefixCut := [⟨9,32561101,32561119⟩,
⟨64,224161461,224161586⟩]
theorem checked55304 : checkPrefixCuts (2^48) 7252738049 10 Manual.Count131072.C055304.packed 64 cuts55304 = true := by
 decide +kernel
def pointBounds55304 : List (Nat × Nat × Nat) := [(7252756480,112908833163109,112909220996532)]
theorem point_links_checked55304 : (cuts55304.take 1).map (fun c => (7252738049-1+2*2^10*c.k,112908800602008+c.lower,112909188435413+c.upper)) = pointBounds55304 := by
 decide +kernel
def cuts55305 : List PrefixCut := [⟨56,199203833,199203946⟩,
⟨64,227921832,227921961⟩]
theorem checked55305 : checkPrefixCuts (2^48) 7252869121 10 Manual.Count131072.C055305.packed 64 cuts55305 = true := by
 decide +kernel
def pointBounds55305 : List (Nat × Nat × Nat) := [(7252983808,112909223967302,112909611800945)]
theorem point_links_checked55305 : (cuts55305.take 1).map (fun c => (7252869121-1+2*2^10*c.k,112909024763469+c.lower,112909412596999+c.upper)) = pointBounds55305 := by
 decide +kernel
def cuts55306 : List PrefixCut := [⟨64,225744458,225744585⟩]
theorem checked55306 : checkPrefixCuts (2^48) 7253000193 10 Manual.Count131072.C055306.packed 64 cuts55306 = true := by
 decide +kernel
def cuts55307 : List PrefixCut := [⟨39,135320529,135320605⟩,
⟨64,224110482,224110608⟩]
theorem checked55307 : checkPrefixCuts (2^48) 7253131265 10 Manual.Count131072.C055307.packed 64 cuts55307 = true := by
 decide +kernel
def pointBounds55307 : List (Nat × Nat × Nat) := [(7253211136,112909613750288,112910001584150)]
theorem point_links_checked55307 : (cuts55307.take 1).map (fun c => (7253131265-1+2*2^10*c.k,112909478429759+c.lower,112909866263545+c.upper)) = pointBounds55307 := by
 decide +kernel
def cuts55308 : List PrefixCut := [⟨64,222321347,222321472⟩]
theorem checked55308 : checkPrefixCuts (2^48) 7253262337 10 Manual.Count131072.C055308.packed 64 cuts55308 = true := by
 decide +kernel
def cuts55309 : List PrefixCut := [⟨22,75089303,75089346⟩,
⟨64,223830746,223830873⟩]
theorem checked55309 : checkPrefixCuts (2^48) 7253393409 10 Manual.Count131072.C055309.packed 64 cuts55309 = true := by
 decide +kernel
def pointBounds55309 : List (Nat × Nat × Nat) := [(7253438464,112909999950891,112910387784971)]
theorem point_links_checked55309 : (cuts55309.take 1).map (fun c => (7253393409-1+2*2^10*c.k,112909924861588+c.lower,112910312695625+c.upper)) = pointBounds55309 := by
 decide +kernel
def cuts55310 : List PrefixCut := [⟨64,227396762,227396890⟩]
theorem checked55310 : checkPrefixCuts (2^48) 7253524481 10 Manual.Count131072.C055310.packed 64 cuts55310 = true := by
 decide +kernel
def cuts55311 : List PrefixCut := [⟨5,17927694,17927704⟩,
⟨64,220058681,220058804⟩]
theorem checked55311 : checkPrefixCuts (2^48) 7253655553 10 Manual.Count131072.C055311.packed 64 cuts55311 = true := by
 decide +kernel
def pointBounds55311 : List (Nat × Nat × Nat) := [(7253665792,112910394016790,112910781851092)]
theorem point_links_checked55311 : (cuts55311.take 1).map (fun c => (7253655553-1+2*2^10*c.k,112910376089096+c.lower,112910763923388+c.upper)) = pointBounds55311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000165
