import PlattAssemblyKernel
import PlattCertificates.Count131072.C064352
import PlattCertificates.Count131072.C064353
import PlattCertificates.Count131072.C064354
import PlattCertificates.Count131072.C064355
import PlattCertificates.Count131072.C064356
import PlattCertificates.Count131072.C064357
import PlattCertificates.Count131072.C064358
import PlattCertificates.Count131072.C064359
import PlattCertificates.Count131072.C064360
import PlattCertificates.Count131072.C064361
import PlattCertificates.Count131072.C064362
import PlattCertificates.Count131072.C064363
import PlattCertificates.Count131072.C064364
import PlattCertificates.Count131072.C064365
import PlattCertificates.Count131072.C064366
import PlattCertificates.Count131072.C064367
import PlattCertificates.Count131072.C064368
import PlattCertificates.Count131072.C064369
import PlattCertificates.Count131072.C064370
import PlattCertificates.Count131072.C064371
import PlattCertificates.Count131072.C064372
import PlattCertificates.Count131072.C064373
import PlattCertificates.Count131072.C064374
import PlattCertificates.Count131072.C064375
import PlattCertificates.Count131072.C064376
import PlattCertificates.Count131072.C064377
import PlattCertificates.Count131072.C064378
import PlattCertificates.Count131072.C064379
import PlattCertificates.Count131072.C064380
import PlattCertificates.Count131072.C064381
import PlattCertificates.Count131072.C064382
import PlattCertificates.Count131072.C064383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000136
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64352 : List PrefixCut := [⟨64,194593496,194593608⟩]
theorem checked64352 : checkPrefixCuts (2^48) 8438677505 10 Manual.Count131072.C064352.packed 64 cuts64352 = true := by
 decide +kernel
def cuts64353 : List PrefixCut := [⟨46,136553843,136553924⟩,
⟨64,189287105,189287212⟩]
theorem checked64353 : checkPrefixCuts (2^48) 8438808577 10 Manual.Count131072.C064353.packed 64 cuts64353 = true := by
 decide +kernel
def pointBounds64353 : List (Nat × Nat × Nat) := [(8438902784,114780462139042,114780851042007)]
theorem point_links_checked64353 : (cuts64353.take 1).map (fun c => (8438808577-1+2*2^10*c.k,114780325585199+c.lower,114780714488083+c.upper)) = pointBounds64353 := by
 decide +kernel
def cuts64354 : List PrefixCut := [⟨64,189784478,189784588⟩]
theorem checked64354 : checkPrefixCuts (2^48) 8438939649 10 Manual.Count131072.C064354.packed 64 cuts64354 = true := by
 decide +kernel
def cuts64355 : List PrefixCut := [⟨47,138850993,138851068⟩,
⟨64,189748175,189748279⟩]
theorem checked64355 : checkPrefixCuts (2^48) 8439070721 10 Manual.Count131072.C064355.packed 64 cuts64355 = true := by
 decide +kernel
def pointBounds64355 : List (Nat × Nat × Nat) := [(8439166976,114780843507775,114781232410951)]
theorem point_links_checked64355 : (cuts64355.take 1).map (fun c => (8439070721-1+2*2^10*c.k,114780704656782+c.lower,114781093559883+c.upper)) = pointBounds64355 := by
 decide +kernel
def cuts64356 : List PrefixCut := [⟨64,191579648,191579759⟩]
theorem checked64356 : checkPrefixCuts (2^48) 8439201793 10 Manual.Count131072.C064356.packed 64 cuts64356 = true := by
 decide +kernel
def cuts64357 : List PrefixCut := [⟨48,142115199,142115284⟩,
⟨64,190442666,190442779⟩]
theorem checked64357 : checkPrefixCuts (2^48) 8439332865 10 Manual.Count131072.C064357.packed 64 cuts64357 = true := by
 decide +kernel
def pointBounds64357 : List (Nat × Nat × Nat) := [(8439431168,114781228099804,114781617003205)]
theorem point_links_checked64357 : (cuts64357.take 1).map (fun c => (8439332865-1+2*2^10*c.k,114781085984605+c.lower,114781474887921+c.upper)) = pointBounds64357 := by
 decide +kernel
def cuts64358 : List PrefixCut := [⟨64,192674304,192674414⟩]
theorem checked64358 : checkPrefixCuts (2^48) 8439463937 10 Manual.Count131072.C064358.packed 64 cuts64358 = true := by
 decide +kernel
def cuts64359 : List PrefixCut := [⟨49,143711650,143711733⟩,
⟨64,188435678,188435784⟩]
theorem checked64359 : checkPrefixCuts (2^48) 8439595009 10 Manual.Count131072.C064359.packed 64 cuts64359 = true := by
 decide +kernel
def pointBounds64359 : List (Nat × Nat × Nat) := [(8439695360,114781612813225,114782001716847)]
theorem point_links_checked64359 : (cuts64359.take 1).map (fun c => (8439595009-1+2*2^10*c.k,114781469101575+c.lower,114781858005114+c.upper)) = pointBounds64359 := by
 decide +kernel
def cuts64360 : List PrefixCut := [⟨64,188832970,188833084⟩]
theorem checked64360 : checkPrefixCuts (2^48) 8439726081 10 Manual.Count131072.C064360.packed 64 cuts64360 = true := by
 decide +kernel
def cuts64361 : List PrefixCut := [⟨50,148976544,148976634⟩,
⟨64,192065014,192065127⟩]
theorem checked64361 : checkPrefixCuts (2^48) 8439857153 10 Manual.Count131072.C064361.packed 64 cuts64361 = true := by
 decide +kernel
def pointBounds64361 : List (Nat × Nat × Nat) := [(8439959552,114781995346767,114782384250616)]
theorem point_links_checked64361 : (cuts64361.take 1).map (fun c => (8439857153-1+2*2^10*c.k,114781846370223+c.lower,114782235273982+c.upper)) = pointBounds64361 := by
 decide +kernel
def cuts64362 : List PrefixCut := [⟨64,187926654,187926761⟩]
theorem checked64362 : checkPrefixCuts (2^48) 8439988225 10 Manual.Count131072.C064362.packed 64 cuts64362 = true := by
 decide +kernel
def cuts64363 : List PrefixCut := [⟨51,151106262,151106353⟩,
⟨64,189491156,189491271⟩]
theorem checked64363 : checkPrefixCuts (2^48) 8440119297 10 Manual.Count131072.C064363.packed 64 cuts64363 = true := by
 decide +kernel
def pointBounds64363 : List (Nat × Nat × Nat) := [(8440223744,114782377468153,114782766372223)]
theorem point_links_checked64363 : (cuts64363.take 1).map (fun c => (8440119297-1+2*2^10*c.k,114782226361891+c.lower,114782615265870+c.upper)) = pointBounds64363 := by
 decide +kernel
def cuts64364 : List PrefixCut := [⟨64,191855975,191856086⟩]
theorem checked64364 : checkPrefixCuts (2^48) 8440250369 10 Manual.Count131072.C064364.packed 64 cuts64364 = true := by
 decide +kernel
def cuts64365 : List PrefixCut := [⟨52,154603132,154603221⟩,
⟨64,189485275,189485386⟩]
theorem checked64365 : checkPrefixCuts (2^48) 8440381441 10 Manual.Count131072.C064365.packed 64 cuts64365 = true := by
 decide +kernel
def pointBounds64365 : List (Nat × Nat × Nat) := [(8440487936,114782762312154,114783151216448)]
theorem point_links_checked64365 : (cuts64365.take 1).map (fun c => (8440381441-1+2*2^10*c.k,114782607709022+c.lower,114782996613227+c.upper)) = pointBounds64365 := by
 decide +kernel
def cuts64366 : List PrefixCut := [⟨64,195451584,195451695⟩]
theorem checked64366 : checkPrefixCuts (2^48) 8440512513 10 Manual.Count131072.C064366.packed 64 cuts64366 = true := by
 decide +kernel
def cuts64367 : List PrefixCut := [⟨53,160600825,160600923⟩,
⟨64,193381012,193381132⟩]
theorem checked64367 : checkPrefixCuts (2^48) 8440643585 10 Manual.Count131072.C064367.packed 64 cuts64367 = true := by
 decide +kernel
def pointBounds64367 : List (Nat × Nat × Nat) := [(8440752128,114783153246706,114783542151231)]
theorem point_links_checked64367 : (cuts64367.take 1).map (fun c => (8440643585-1+2*2^10*c.k,114782992645881+c.lower,114783381550308+c.upper)) = pointBounds64367 := by
 decide +kernel
def cuts64368 : List PrefixCut := [⟨64,192744420,192744524⟩]
theorem checked64368 : checkPrefixCuts (2^48) 8440774657 10 Manual.Count131072.C064368.packed 64 cuts64368 = true := by
 decide +kernel
def cuts64369 : List PrefixCut := [⟨54,163063450,163063545⟩,
⟨64,193508393,193508507⟩]
theorem checked64369 : checkPrefixCuts (2^48) 8440905729 10 Manual.Count131072.C064369.packed 64 cuts64369 = true := by
 decide +kernel
def pointBounds64369 : List (Nat × Nat × Nat) := [(8441016320,114783541834763,114783930739509)]
theorem point_links_checked64369 : (cuts64369.take 1).map (fun c => (8440905729-1+2*2^10*c.k,114783378771313+c.lower,114783767675964+c.upper)) = pointBounds64369 := by
 decide +kernel
def cuts64370 : List PrefixCut := [⟨64,189470564,189470678⟩]
theorem checked64370 : checkPrefixCuts (2^48) 8441036801 10 Manual.Count131072.C064370.packed 64 cuts64370 = true := by
 decide +kernel
def cuts64371 : List PrefixCut := [⟨55,161791251,161791348⟩,
⟨64,189901097,189901208⟩]
theorem checked64371 : checkPrefixCuts (2^48) 8441167873 10 Manual.Count131072.C064371.packed 64 cuts64371 = true := by
 decide +kernel
def pointBounds64371 : List (Nat × Nat × Nat) := [(8441280512,114783923541521,114784312446497)]
theorem point_links_checked64371 : (cuts64371.take 1).map (fun c => (8441167873-1+2*2^10*c.k,114783761750270+c.lower,114784150655149+c.upper)) = pointBounds64371 := by
 decide +kernel
def cuts64372 : List PrefixCut := [⟨64,190565052,190565164⟩]
theorem checked64372 : checkPrefixCuts (2^48) 8441298945 10 Manual.Count131072.C064372.packed 64 cuts64372 = true := by
 decide +kernel
def cuts64373 : List PrefixCut := [⟨56,169422023,169422122⟩,
⟨64,192996210,192996324⟩]
theorem checked64373 : checkPrefixCuts (2^48) 8441430017 10 Manual.Count131072.C064373.packed 64 cuts64373 = true := by
 decide +kernel
def pointBounds64373 : List (Nat × Nat × Nat) := [(8441544704,114784311638442,114784700543643)]
theorem point_links_checked64373 : (cuts64373.take 1).map (fun c => (8441430017-1+2*2^10*c.k,114784142216419+c.lower,114784531121521+c.upper)) = pointBounds64373 := by
 decide +kernel
def cuts64374 : List PrefixCut := [⟨64,192092936,192093049⟩]
theorem checked64374 : checkPrefixCuts (2^48) 8441561089 10 Manual.Count131072.C064374.packed 64 cuts64374 = true := by
 decide +kernel
def cuts64375 : List PrefixCut := [⟨57,170783829,170783924⟩,
⟨64,193256964,193257073⟩]
theorem checked64375 : checkPrefixCuts (2^48) 8441692161 10 Manual.Count131072.C064375.packed 64 cuts64375 = true := by
 decide +kernel
def pointBounds64375 : List (Nat × Nat × Nat) := [(8441808896,114784698089394,114785086994818)]
theorem point_links_checked64375 : (cuts64375.take 1).map (fun c => (8441692161-1+2*2^10*c.k,114784527305565+c.lower,114784916210894+c.upper)) = pointBounds64375 := by
 decide +kernel
def cuts64376 : List PrefixCut := [⟨64,190653234,190653344⟩]
theorem checked64376 : checkPrefixCuts (2^48) 8441823233 10 Manual.Count131072.C064376.packed 64 cuts64376 = true := by
 decide +kernel
def cuts64377 : List PrefixCut := [⟨58,172745692,172745788⟩,
⟨64,190950365,190950472⟩]
theorem checked64377 : checkPrefixCuts (2^48) 8441954305 10 Manual.Count131072.C064377.packed 64 cuts64377 = true := by
 decide +kernel
def pointBounds64377 : List (Nat × Nat × Nat) := [(8442073088,114785083961455,114785472867099)]
theorem point_links_checked64377 : (cuts64377.take 1).map (fun c => (8441954305-1+2*2^10*c.k,114784911215763+c.lower,114785300121311+c.upper)) = pointBounds64377 := by
 decide +kernel
def cuts64378 : List PrefixCut := [⟨64,192281046,192281163⟩]
theorem checked64378 : checkPrefixCuts (2^48) 8442085377 10 Manual.Count131072.C064378.packed 64 cuts64378 = true := by
 decide +kernel
def cuts64379 : List PrefixCut := [⟨59,176407836,176407943⟩,
⟨64,191944674,191944790⟩]
theorem checked64379 : checkPrefixCuts (2^48) 8442216449 10 Manual.Count131072.C064379.packed 64 cuts64379 = true := by
 decide +kernel
def pointBounds64379 : List (Nat × Nat × Nat) := [(8442337280,114785470855010,114785859760889)]
theorem point_links_checked64379 : (cuts64379.take 1).map (fun c => (8442216449-1+2*2^10*c.k,114785294447174+c.lower,114785683352946+c.upper)) = pointBounds64379 := by
 decide +kernel
def cuts64380 : List PrefixCut := [⟨64,189441139,189441246⟩]
theorem checked64380 : checkPrefixCuts (2^48) 8442347521 10 Manual.Count131072.C064380.packed 64 cuts64380 = true := by
 decide +kernel
def cuts64381 : List PrefixCut := [⟨60,176735726,176735829⟩,
⟨64,188704720,188704828⟩]
theorem checked64381 : checkPrefixCuts (2^48) 8442478593 10 Manual.Count131072.C064381.packed 64 cuts64381 = true := by
 decide +kernel
def pointBounds64381 : List (Nat × Nat × Nat) := [(8442601472,114785852568713,114786241474811)]
theorem point_links_checked64381 : (cuts64381.take 1).map (fun c => (8442478593-1+2*2^10*c.k,114785675832987+c.lower,114786064738982+c.upper)) = pointBounds64381 := by
 decide +kernel
def cuts64382 : List PrefixCut := [⟨64,190702162,190702270⟩]
theorem checked64382 : checkPrefixCuts (2^48) 8442609665 10 Manual.Count131072.C064382.packed 64 cuts64382 = true := by
 decide +kernel
def cuts64383 : List PrefixCut := [⟨61,179730731,179730832⟩,
⟨64,188898893,188899000⟩]
theorem checked64383 : checkPrefixCuts (2^48) 8442740737 10 Manual.Count131072.C064383.packed 64 cuts64383 = true := by
 decide +kernel
def pointBounds64383 : List (Nat × Nat × Nat) := [(8442865664,114786234970600,114786623876912)]
theorem point_links_checked64383 : (cuts64383.take 1).map (fun c => (8442740737-1+2*2^10*c.k,114786055239869+c.lower,114786444146080+c.upper)) = pointBounds64383 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000136
