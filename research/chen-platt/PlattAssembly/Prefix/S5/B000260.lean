import PlattAssemblyKernel
import PlattCertificates.Count131072.C048320
import PlattCertificates.Count131072.C048321
import PlattCertificates.Count131072.C048322
import PlattCertificates.Count131072.C048323
import PlattCertificates.Count131072.C048324
import PlattCertificates.Count131072.C048325
import PlattCertificates.Count131072.C048326
import PlattCertificates.Count131072.C048327
import PlattCertificates.Count131072.C048328
import PlattCertificates.Count131072.C048329
import PlattCertificates.Count131072.C048330
import PlattCertificates.Count131072.C048331
import PlattCertificates.Count131072.C048332
import PlattCertificates.Count131072.C048333
import PlattCertificates.Count131072.C048334
import PlattCertificates.Count131072.C048335
import PlattCertificates.Count131072.C048336
import PlattCertificates.Count131072.C048337
import PlattCertificates.Count131072.C048338
import PlattCertificates.Count131072.C048339
import PlattCertificates.Count131072.C048340
import PlattCertificates.Count131072.C048341
import PlattCertificates.Count131072.C048342
import PlattCertificates.Count131072.C048343
import PlattCertificates.Count131072.C048344
import PlattCertificates.Count131072.C048345
import PlattCertificates.Count131072.C048346
import PlattCertificates.Count131072.C048347
import PlattCertificates.Count131072.C048348
import PlattCertificates.Count131072.C048349
import PlattCertificates.Count131072.C048350
import PlattCertificates.Count131072.C048351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000260
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48320 : List PrefixCut := [⟨64,262136806,262136954⟩]
theorem checked48320 : checkPrefixCuts (2^48) 6337331201 10 Manual.Count131072.C048320.packed 64 cuts48320 = true := by
 decide +kernel
def cuts48321 : List PrefixCut := [⟨23,93003511,93003566⟩,
⟨64,259644178,259644327⟩]
theorem checked48321 : checkPrefixCuts (2^48) 6337462273 10 Manual.Count131072.C048321.packed 64 cuts48321 = true := by
 decide +kernel
def pointBounds48321 : List (Nat × Nat × Nat) := [(6337509376,111231595948935,111231982828385)]
theorem point_links_checked48321 : (cuts48321.take 1).map (fun c => (6337462273-1+2*2^10*c.k,111231502945424+c.lower,111231889824819+c.upper)) = pointBounds48321 := by
 decide +kernel
def cuts48322 : List PrefixCut := [⟨56,231125918,231126045⟩,
⟨64,263280691,263280838⟩]
theorem checked48322 : checkPrefixCuts (2^48) 6337593345 10 Manual.Count131072.C048322.packed 64 cuts48322 = true := by
 decide +kernel
def pointBounds48322 : List (Nat × Nat × Nat) := [(6337708032,111231993715520,111232380595191)]
theorem point_links_checked48322 : (cuts48322.take 1).map (fun c => (6337593345-1+2*2^10*c.k,111231762589602+c.lower,111232149469146+c.upper)) = pointBounds48322 := by
 decide +kernel
def cuts48323 : List PrefixCut := [⟨64,258123415,258123563⟩]
theorem checked48323 : checkPrefixCuts (2^48) 6337724417 10 Manual.Count131072.C048323.packed 64 cuts48323 = true := by
 decide +kernel
def cuts48324 : List PrefixCut := [⟨25,99437371,99437429⟩,
⟨64,257451909,257452060⟩]
theorem checked48324 : checkPrefixCuts (2^48) 6337855489 10 Manual.Count131072.C048324.packed 64 cuts48324 = true := by
 decide +kernel
def pointBounds48324 : List (Nat × Nat × Nat) := [(6337906688,111232383431079,111232770310976)]
theorem point_links_checked48324 : (cuts48324.take 1).map (fun c => (6337855489-1+2*2^10*c.k,111232283993708+c.lower,111232670873547+c.upper)) = pointBounds48324 := by
 decide +kernel
def cuts48325 : List PrefixCut := [⟨58,231822065,231822205⟩,
⟨64,256114280,256114435⟩]
theorem checked48325 : checkPrefixCuts (2^48) 6337986561 10 Manual.Count131072.C048325.packed 64 cuts48325 = true := by
 decide +kernel
def pointBounds48325 : List (Nat × Nat × Nat) := [(6338105344,111232773267682,111233160147812)]
theorem point_links_checked48325 : (cuts48325.take 1).map (fun c => (6337986561-1+2*2^10*c.k,111232541445617+c.lower,111232928325607+c.upper)) = pointBounds48325 := by
 decide +kernel
def cuts48326 : List PrefixCut := [⟨64,253888486,253888637⟩]
theorem checked48326 : checkPrefixCuts (2^48) 6338117633 10 Manual.Count131072.C048326.packed 64 cuts48326 = true := by
 decide +kernel
def cuts48327 : List PrefixCut := [⟨27,108135290,108135353⟩,
⟨64,256014886,256015033⟩]
theorem checked48327 : checkPrefixCuts (2^48) 6338248705 10 Manual.Count131072.C048327.packed 64 cuts48327 = true := by
 decide +kernel
def pointBounds48327 : List (Nat × Nat × Nat) := [(6338304000,111233159583673,111233546464032)]
theorem point_links_checked48327 : (cuts48327.take 1).map (fun c => (6338248705-1+2*2^10*c.k,111233051448383+c.lower,111233438328679+c.upper)) = pointBounds48327 := by
 decide +kernel
def cuts48328 : List PrefixCut := [⟨60,242731884,242732026⟩,
⟨64,258496416,258496567⟩]
theorem checked48328 : checkPrefixCuts (2^48) 6338379777 10 Manual.Count131072.C048328.packed 64 cuts48328 = true := by
 decide +kernel
def pointBounds48328 : List (Nat × Nat × Nat) := [(6338502656,111233550195153,111233937075738)]
theorem point_links_checked48328 : (cuts48328.take 1).map (fun c => (6338379777-1+2*2^10*c.k,111233307463269+c.lower,111233694343712+c.upper)) = pointBounds48328 := by
 decide +kernel
def cuts48329 : List PrefixCut := [⟨64,254894124,254894271⟩]
theorem checked48329 : checkPrefixCuts (2^48) 6338510849 10 Manual.Count131072.C048329.packed 64 cuts48329 = true := by
 decide +kernel
def cuts48330 : List PrefixCut := [⟨29,117364996,117365063⟩,
⟨64,255865784,255865929⟩]
theorem checked48330 : checkPrefixCuts (2^48) 6338641921 10 Manual.Count131072.C048330.packed 64 cuts48330 = true := by
 decide +kernel
def pointBounds48330 : List (Nat × Nat × Nat) := [(6338701312,111233938218805,111234325099613)]
theorem point_links_checked48330 : (cuts48330.take 1).map (fun c => (6338641921-1+2*2^10*c.k,111233820853809+c.lower,111234207734550+c.upper)) = pointBounds48330 := by
 decide +kernel
def cuts48331 : List PrefixCut := [⟨62,244981388,244981525⟩,
⟨64,252263703,252263844⟩]
theorem checked48331 : checkPrefixCuts (2^48) 6338772993 10 Manual.Count131072.C048331.packed 64 cuts48331 = true := by
 decide +kernel
def pointBounds48331 : List (Nat × Nat × Nat) := [(6338899968,111234321700981,111234708582004)]
theorem point_links_checked48331 : (cuts48331.take 1).map (fun c => (6338772993-1+2*2^10*c.k,111234076719593+c.lower,111234463600479+c.upper)) = pointBounds48331 := by
 decide +kernel
def cuts48332 : List PrefixCut := [⟨64,256698858,256699005⟩]
theorem checked48332 : checkPrefixCuts (2^48) 6338904065 10 Manual.Count131072.C048332.packed 64 cuts48332 = true := by
 decide +kernel
def cuts48333 : List PrefixCut := [⟨31,124773008,124773081⟩,
⟨64,256071927,256072079⟩]
theorem checked48333 : checkPrefixCuts (2^48) 6339035137 10 Manual.Count131072.C048333.packed 64 cuts48333 = true := by
 decide +kernel
def pointBounds48333 : List (Nat × Nat × Nat) := [(6339098624,111234710455162,111235097336409)]
theorem point_links_checked48333 : (cuts48333.take 1).map (fun c => (6339035137-1+2*2^10*c.k,111234585682154+c.lower,111234972563328+c.upper)) = pointBounds48333 := by
 decide +kernel
def cuts48334 : List PrefixCut := [⟨64,259307977,259308124⟩]
theorem checked48334 : checkPrefixCuts (2^48) 6339166209 10 Manual.Count131072.C048334.packed 64 cuts48334 = true := by
 decide +kernel
def pointBounds48334 : List (Nat × Nat × Nat) := [(6339297280,111235101062058,111235487943531)]
theorem point_links_checked48334 : (cuts48334.take 1).map (fun c => (6339166209-1+2*2^10*c.k,111234841754081+c.lower,111235228635407+c.upper)) = pointBounds48334 := by
 decide +kernel
def cuts48335 : List PrefixCut := [⟨64,257171365,257171509⟩]
theorem checked48335 : checkPrefixCuts (2^48) 6339297281 10 Manual.Count131072.C048335.packed 64 cuts48335 = true := by
 decide +kernel
def cuts48336 : List PrefixCut := [⟨33,130137680,130137756⟩,
⟨64,256011617,256011765⟩]
theorem checked48336 : checkPrefixCuts (2^48) 6339428353 10 Manual.Count131072.C048336.packed 64 cuts48336 = true := by
 decide +kernel
def pointBounds48336 : List (Nat × Nat × Nat) := [(6339495936,111235488371103,111235875252796)]
theorem point_links_checked48336 : (cuts48336.take 1).map (fun c => (6339428353-1+2*2^10*c.k,111235358233423+c.lower,111235745115040+c.upper)) = pointBounds48336 := by
 decide +kernel
def cuts48337 : List PrefixCut := [⟨64,258315109,258315249⟩]
theorem checked48337 : checkPrefixCuts (2^48) 6339559425 10 Manual.Count131072.C048337.packed 64 cuts48337 = true := by
 decide +kernel
def cuts48338 : List PrefixCut := [⟨2,8036187,8036191⟩,
⟨64,256489424,256489567⟩]
theorem checked48338 : checkPrefixCuts (2^48) 6339690497 10 Manual.Count131072.C048338.packed 64 cuts48338 = true := by
 decide +kernel
def pointBounds48338 : List (Nat × Nat × Nat) := [(6339694592,111235880596336,111236267478245)]
theorem point_links_checked48338 : (cuts48338.take 1).map (fun c => (6339690497-1+2*2^10*c.k,111235872560149+c.lower,111236259442054+c.upper)) = pointBounds48338 := by
 decide +kernel
def cuts48339 : List PrefixCut := [⟨35,140829405,140829490⟩,
⟨64,258526409,258526560⟩]
theorem checked48339 : checkPrefixCuts (2^48) 6339821569 10 Manual.Count131072.C048339.packed 64 cuts48339 = true := by
 decide +kernel
def pointBounds48339 : List (Nat × Nat × Nat) := [(6339893248,111236269878978,111236656761111)]
theorem point_links_checked48339 : (cuts48339.take 1).map (fun c => (6339821569-1+2*2^10*c.k,111236129049573+c.lower,111236515931621+c.upper)) = pointBounds48339 := by
 decide +kernel
def cuts48340 : List PrefixCut := [⟨64,259142645,259142794⟩]
theorem checked48340 : checkPrefixCuts (2^48) 6339952641 10 Manual.Count131072.C048340.packed 64 cuts48340 = true := by
 decide +kernel
def cuts48341 : List PrefixCut := [⟨4,16914898,16914908⟩,
⟨64,255985185,255985336⟩]
theorem checked48341 : checkPrefixCuts (2^48) 6340083713 10 Manual.Count131072.C048341.packed 64 cuts48341 = true := by
 decide +kernel
def pointBounds48341 : List (Nat × Nat × Nat) := [(6340091904,111236663633525,111237050515883)]
theorem point_links_checked48341 : (cuts48341.take 1).map (fun c => (6340083713-1+2*2^10*c.k,111236646718627+c.lower,111237033600975+c.upper)) = pointBounds48341 := by
 decide +kernel
def cuts48342 : List PrefixCut := [⟨37,148057000,148057080⟩,
⟨64,256956566,256956707⟩]
theorem checked48342 : checkPrefixCuts (2^48) 6340214785 10 Manual.Count131072.C048342.packed 64 cuts48342 = true := by
 decide +kernel
def pointBounds48342 : List (Nat × Nat × Nat) := [(6340290560,111237050760812,111237437643391)]
theorem point_links_checked48342 : (cuts48342.take 1).map (fun c => (6340214785-1+2*2^10*c.k,111236902703812+c.lower,111237289586311+c.upper)) = pointBounds48342 := by
 decide +kernel
def cuts48343 : List PrefixCut := [⟨64,255797008,255797149⟩]
theorem checked48343 : checkPrefixCuts (2^48) 6340345857 10 Manual.Count131072.C048343.packed 64 cuts48343 = true := by
 decide +kernel
def cuts48344 : List PrefixCut := [⟨6,23661623,23661635⟩,
⟨64,258410933,258411075⟩]
theorem checked48344 : checkPrefixCuts (2^48) 6340476929 10 Manual.Count131072.C048344.packed 64 cuts48344 = true := by
 decide +kernel
def pointBounds48344 : List (Nat × Nat × Nat) := [(6340489216,111237439119009,111237826001802)]
theorem point_links_checked48344 : (cuts48344.take 1).map (fun c => (6340476929-1+2*2^10*c.k,111237415457386+c.lower,111237802340167+c.upper)) = pointBounds48344 := by
 decide +kernel
def cuts48345 : List PrefixCut := [⟨39,155416874,155416962⟩,
⟨64,255031791,255031937⟩]
theorem checked48345 : checkPrefixCuts (2^48) 6340608001 10 Manual.Count131072.C048345.packed 64 cuts48345 = true := by
 decide +kernel
def pointBounds48345 : List (Nat × Nat × Nat) := [(6340687872,111237829285193,111238216168204)]
theorem point_links_checked48345 : (cuts48345.take 1).map (fun c => (6340608001-1+2*2^10*c.k,111237673868319+c.lower,111238060751242+c.upper)) = pointBounds48345 := by
 decide +kernel
def cuts48346 : List PrefixCut := [⟨64,261551992,261552138⟩]
theorem checked48346 : checkPrefixCuts (2^48) 6340739073 10 Manual.Count131072.C048346.packed 64 cuts48346 = true := by
 decide +kernel
def cuts48347 : List PrefixCut := [⟨8,31472880,31472899⟩,
⟨64,255154412,255154558⟩]
theorem checked48347 : checkPrefixCuts (2^48) 6340870145 10 Manual.Count131072.C048347.packed 64 cuts48347 = true := by
 decide +kernel
def pointBounds48347 : List (Nat × Nat × Nat) := [(6340886528,111238221924982,111238608808216)]
theorem point_links_checked48347 : (cuts48347.take 1).map (fun c => (6340870145-1+2*2^10*c.k,111238190452102+c.lower,111238577335317+c.upper)) = pointBounds48347 := by
 decide +kernel
def cuts48348 : List PrefixCut := [⟨41,167614252,167614345⟩,
⟨64,263050407,263050553⟩]
theorem checked48348 : checkPrefixCuts (2^48) 6341001217 10 Manual.Count131072.C048348.packed 64 cuts48348 = true := by
 decide +kernel
def pointBounds48348 : List (Nat × Nat × Nat) := [(6341085184,111238613220766,111239000104220)]
theorem point_links_checked48348 : (cuts48348.take 1).map (fun c => (6341001217-1+2*2^10*c.k,111238445606514+c.lower,111238832489875+c.upper)) = pointBounds48348 := by
 decide +kernel
def cuts48349 : List PrefixCut := [⟨64,256519868,256520023⟩]
theorem checked48349 : checkPrefixCuts (2^48) 6341132289 10 Manual.Count131072.C048349.packed 64 cuts48349 = true := by
 decide +kernel
def cuts48350 : List PrefixCut := [⟨10,39815816,39815838⟩,
⟨64,257313556,257313705⟩]
theorem checked48350 : checkPrefixCuts (2^48) 6341263361 10 Manual.Count131072.C048350.packed 64 cuts48350 = true := by
 decide +kernel
def pointBounds48350 : List (Nat × Nat × Nat) := [(6341283840,111239004992605,111239391876289)]
theorem point_links_checked48350 : (cuts48350.take 1).map (fun c => (6341263361-1+2*2^10*c.k,111238965176789+c.lower,111239352060451+c.upper)) = pointBounds48350 := by
 decide +kernel
def cuts48351 : List PrefixCut := [⟨43,172264401,172264500⟩,
⟨64,256376142,256376290⟩]
theorem checked48351 : checkPrefixCuts (2^48) 6341394433 10 Manual.Count131072.C048351.packed 64 cuts48351 = true := by
 decide +kernel
def pointBounds48351 : List (Nat × Nat × Nat) := [(6341482496,111239394754746,111239781638656)]
theorem point_links_checked48351 : (cuts48351.take 1).map (fun c => (6341394433-1+2*2^10*c.k,111239222490345+c.lower,111239609374156+c.upper)) = pointBounds48351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000260
