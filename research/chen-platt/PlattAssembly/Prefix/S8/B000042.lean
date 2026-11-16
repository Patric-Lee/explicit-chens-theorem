import PlattAssemblyKernel
import PlattCertificates.Count131072.C071344
import PlattCertificates.Count131072.C071345
import PlattCertificates.Count131072.C071346
import PlattCertificates.Count131072.C071347
import PlattCertificates.Count131072.C071348
import PlattCertificates.Count131072.C071349
import PlattCertificates.Count131072.C071350
import PlattCertificates.Count131072.C071351
import PlattCertificates.Count131072.C071352
import PlattCertificates.Count131072.C071353
import PlattCertificates.Count131072.C071354
import PlattCertificates.Count131072.C071355
import PlattCertificates.Count131072.C071356
import PlattCertificates.Count131072.C071357
import PlattCertificates.Count131072.C071358
import PlattCertificates.Count131072.C071359
import PlattCertificates.Count131072.C071360
import PlattCertificates.Count131072.C071361
import PlattCertificates.Count131072.C071362
import PlattCertificates.Count131072.C071363
import PlattCertificates.Count131072.C071364
import PlattCertificates.Count131072.C071365
import PlattCertificates.Count131072.C071366
import PlattCertificates.Count131072.C071367
import PlattCertificates.Count131072.C071368
import PlattCertificates.Count131072.C071369
import PlattCertificates.Count131072.C071370
import PlattCertificates.Count131072.C071371
import PlattCertificates.Count131072.C071372
import PlattCertificates.Count131072.C071373
import PlattCertificates.Count131072.C071374
import PlattCertificates.Count131072.C071375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71344 : List PrefixCut := [⟨64,172852903,172853004⟩]
theorem checked71344 : checkPrefixCuts (2^48) 9355132929 10 Manual.Count131072.C071344.packed 64 cuts71344 = true := by
 decide +kernel
def cuts71345 : List PrefixCut := [⟨38,102928315,102928377⟩,
⟨64,172639877,172639979⟩]
theorem checked71345 : checkPrefixCuts (2^48) 9355264001 10 Manual.Count131072.C071345.packed 64 cuts71345 = true := by
 decide +kernel
def pointBounds71345 : List (Nat × Nat × Nat) := [(9355341824,116047186248125,116047575891080)]
theorem point_links_checked71345 : (cuts71345.take 1).map (fun c => (9355264001-1+2*2^10*c.k,116047083319810+c.lower,116047472962703+c.upper)) = pointBounds71345 := by
 decide +kernel
def cuts71346 : List PrefixCut := [⟨64,172667540,172667647⟩]
theorem checked71346 : checkPrefixCuts (2^48) 9355395073 10 Manual.Count131072.C071346.packed 64 cuts71346 = true := by
 decide +kernel
def cuts71347 : List PrefixCut := [⟨53,141736613,141736699⟩,
⟨64,171281162,171281266⟩]
theorem checked71347 : checkPrefixCuts (2^48) 9355526145 10 Manual.Count131072.C071347.packed 64 cuts71347 = true := by
 decide +kernel
def pointBounds71347 : List (Nat × Nat × Nat) := [(9355634688,116047570363840,116047960007028)]
theorem point_links_checked71347 : (cuts71347.take 1).map (fun c => (9355526145-1+2*2^10*c.k,116047428627227+c.lower,116047818270329+c.upper)) = pointBounds71347 := by
 decide +kernel
def cuts71348 : List PrefixCut := [⟨64,172000813,172000910⟩]
theorem checked71348 : checkPrefixCuts (2^48) 9355657217 10 Manual.Count131072.C071348.packed 64 cuts71348 = true := by
 decide +kernel
def cuts71349 : List PrefixCut := [⟨64,171998417,171998513⟩]
theorem checked71349 : checkPrefixCuts (2^48) 9355788289 10 Manual.Count131072.C071349.packed 64 cuts71349 = true := by
 decide +kernel
def cuts71350 : List PrefixCut := [⟨4,10680249,10680255⟩,
⟨64,171213789,171213899⟩]
theorem checked71350 : checkPrefixCuts (2^48) 9355919361 10 Manual.Count131072.C071350.packed 64 cuts71350 = true := by
 decide +kernel
def pointBounds71350 : List (Nat × Nat × Nat) := [(9355927552,116047954587868,116048344231273)]
theorem point_links_checked71350 : (cuts71350.take 1).map (fun c => (9355919361-1+2*2^10*c.k,116047943907619+c.lower,116048333551018+c.upper)) = pointBounds71350 := by
 decide +kernel
def cuts71351 : List PrefixCut := [⟨64,170820296,170820394⟩]
theorem checked71351 : checkPrefixCuts (2^48) 9356050433 10 Manual.Count131072.C071351.packed 64 cuts71351 = true := by
 decide +kernel
def cuts71352 : List PrefixCut := [⟨19,51323839,51323871⟩,
⟨64,173044121,173044224⟩]
theorem checked71352 : checkPrefixCuts (2^48) 9356181505 10 Manual.Count131072.C071352.packed 64 cuts71352 = true := by
 decide +kernel
def pointBounds71352 : List (Nat × Nat × Nat) := [(9356220416,116048337265543,116048726909182)]
theorem point_links_checked71352 : (cuts71352.take 1).map (fun c => (9356181505-1+2*2^10*c.k,116048285941704+c.lower,116048675585311+c.upper)) = pointBounds71352 := by
 decide +kernel
def cuts71353 : List PrefixCut := [⟨64,170243912,170244009⟩]
theorem checked71353 : checkPrefixCuts (2^48) 9356312577 10 Manual.Count131072.C071353.packed 64 cuts71353 = true := by
 decide +kernel
def cuts71354 : List PrefixCut := [⟨34,87512680,87512734⟩,
⟨64,165879449,165879549⟩]
theorem checked71354 : checkPrefixCuts (2^48) 9356443649 10 Manual.Count131072.C071354.packed 64 cuts71354 = true := by
 decide +kernel
def pointBounds71354 : List (Nat × Nat × Nat) := [(9356513280,116048716742417,116049106386278)]
theorem point_links_checked71354 : (cuts71354.take 1).map (fun c => (9356443649-1+2*2^10*c.k,116048629229737+c.lower,116049018873544+c.upper)) = pointBounds71354 := by
 decide +kernel
def cuts71355 : List PrefixCut := [⟨64,170810724,170810817⟩]
theorem checked71355 : checkPrefixCuts (2^48) 9356574721 10 Manual.Count131072.C071355.packed 64 cuts71355 = true := by
 decide +kernel
def cuts71356 : List PrefixCut := [⟨49,130528097,130528170⟩,
⟨64,170687994,170688093⟩]
theorem checked71356 : checkPrefixCuts (2^48) 9356705793 10 Manual.Count131072.C071356.packed 64 cuts71356 = true := by
 decide +kernel
def pointBounds71356 : List (Nat × Nat × Nat) := [(9356806144,116049096448007,116049486092080)]
theorem point_links_checked71356 : (cuts71356.take 1).map (fun c => (9356705793-1+2*2^10*c.k,116048965919910+c.lower,116049355563910+c.upper)) = pointBounds71356 := by
 decide +kernel
def cuts71357 : List PrefixCut := [⟨64,172610862,172610966⟩]
theorem checked71357 : checkPrefixCuts (2^48) 9356836865 10 Manual.Count131072.C071357.packed 64 cuts71357 = true := by
 decide +kernel
def cuts71358 : List PrefixCut := [⟨64,171044193,171044293⟩]
theorem checked71358 : checkPrefixCuts (2^48) 9356967937 10 Manual.Count131072.C071358.packed 64 cuts71358 = true := by
 decide +kernel
def pointBounds71358 : List (Nat × Nat × Nat) := [(9357099008,116049480262959,116049869907262)]
theorem point_links_checked71358 : (cuts71358.take 1).map (fun c => (9356967937-1+2*2^10*c.k,116049309218766+c.lower,116049698862969+c.upper)) = pointBounds71358 := by
 decide +kernel
def cuts71359 : List PrefixCut := [⟨64,171462937,171463042⟩]
theorem checked71359 : checkPrefixCuts (2^48) 9357099009 10 Manual.Count131072.C071359.packed 64 cuts71359 = true := by
 decide +kernel
def cuts71360 : List PrefixCut := [⟨64,174408448,174408558⟩]
theorem checked71360 : checkPrefixCuts (2^48) 9357230081 10 Manual.Count131072.C071360.packed 64 cuts71360 = true := by
 decide +kernel
def cuts71361 : List PrefixCut := [⟨15,39616064,39616089⟩,
⟨64,172390622,172390725⟩]
theorem checked71361 : checkPrefixCuts (2^48) 9357361153 10 Manual.Count131072.C071361.packed 64 cuts71361 = true := by
 decide +kernel
def pointBounds71361 : List (Nat × Nat × Nat) := [(9357391872,116049865750408,116050255394951)]
theorem point_links_checked71361 : (cuts71361.take 1).map (fun c => (9357361153-1+2*2^10*c.k,116049826134344+c.lower,116050215778862+c.upper)) = pointBounds71361 := by
 decide +kernel
def cuts71362 : List PrefixCut := [⟨64,172027242,172027344⟩]
theorem checked71362 : checkPrefixCuts (2^48) 9357492225 10 Manual.Count131072.C071362.packed 64 cuts71362 = true := by
 decide +kernel
def cuts71363 : List PrefixCut := [⟨30,82087347,82087396⟩,
⟨64,172145165,172145263⟩]
theorem checked71363 : checkPrefixCuts (2^48) 9357623297 10 Manual.Count131072.C071363.packed 64 cuts71363 = true := by
 decide +kernel
def pointBounds71363 : List (Nat × Nat × Nat) := [(9357684736,116050252639555,116050642284327)]
theorem point_links_checked71363 : (cuts71363.take 1).map (fun c => (9357623297-1+2*2^10*c.k,116050170552208+c.lower,116050560196931+c.upper)) = pointBounds71363 := by
 decide +kernel
def cuts71364 : List PrefixCut := [⟨64,172112675,172112775⟩]
theorem checked71364 : checkPrefixCuts (2^48) 9357754369 10 Manual.Count131072.C071364.packed 64 cuts71364 = true := by
 decide +kernel
def cuts71365 : List PrefixCut := [⟨45,120375158,120375232⟩,
⟨64,172501268,172501375⟩]
theorem checked71365 : checkPrefixCuts (2^48) 9357885441 10 Manual.Count131072.C071365.packed 64 cuts71365 = true := by
 decide +kernel
def pointBounds71365 : List (Nat × Nat × Nat) := [(9357977600,116050635185206,116051024830201)]
theorem point_links_checked71365 : (cuts71365.take 1).map (fun c => (9357885441-1+2*2^10*c.k,116050514810048+c.lower,116050904454969+c.upper)) = pointBounds71365 := by
 decide +kernel
def cuts71366 : List PrefixCut := [⟨64,170062526,170062627⟩]
theorem checked71366 : checkPrefixCuts (2^48) 9358016513 10 Manual.Count131072.C071366.packed 64 cuts71366 = true := by
 decide +kernel
def cuts71367 : List PrefixCut := [⟨60,162901675,162901769⟩,
⟨64,174120638,174120739⟩]
theorem checked71367 : checkPrefixCuts (2^48) 9358147585 10 Manual.Count131072.C071367.packed 64 cuts71367 = true := by
 decide +kernel
def pointBounds71367 : List (Nat × Nat × Nat) := [(9358270464,116051020275517,116051409920740)]
theorem point_links_checked71367 : (cuts71367.take 1).map (fun c => (9358147585-1+2*2^10*c.k,116050857373842+c.lower,116051247018971+c.upper)) = pointBounds71367 := by
 decide +kernel
def cuts71368 : List PrefixCut := [⟨64,173636982,173637088⟩]
theorem checked71368 : checkPrefixCuts (2^48) 9358278657 10 Manual.Count131072.C071368.packed 64 cuts71368 = true := by
 decide +kernel
def cuts71369 : List PrefixCut := [⟨64,171378764,171378868⟩]
theorem checked71369 : checkPrefixCuts (2^48) 9358409729 10 Manual.Count131072.C071369.packed 64 cuts71369 = true := by
 decide +kernel
def cuts71370 : List PrefixCut := [⟨11,28783455,28783474⟩,
⟨64,171737283,171737386⟩]
theorem checked71370 : checkPrefixCuts (2^48) 9358540801 10 Manual.Count131072.C071370.packed 64 cuts71370 = true := by
 decide +kernel
def pointBounds71370 : List (Nat × Nat × Nat) := [(9358563328,116051405293681,116051794939140)]
theorem point_links_checked71370 : (cuts71370.take 1).map (fun c => (9358540801-1+2*2^10*c.k,116051376510226+c.lower,116051766155666+c.upper)) = pointBounds71370 := by
 decide +kernel
def cuts71371 : List PrefixCut := [⟨64,170652149,170652245⟩]
theorem checked71371 : checkPrefixCuts (2^48) 9358671873 10 Manual.Count131072.C071371.packed 64 cuts71371 = true := by
 decide +kernel
def cuts71372 : List PrefixCut := [⟨26,70136913,70136953⟩,
⟨64,173446783,173446882⟩]
theorem checked71372 : checkPrefixCuts (2^48) 9358802945 10 Manual.Count131072.C071372.packed 64 cuts71372 = true := by
 decide +kernel
def pointBounds71372 : List (Nat × Nat × Nat) := [(9358856192,116051789036571,116052178682250)]
theorem point_links_checked71372 : (cuts71372.take 1).map (fun c => (9358802945-1+2*2^10*c.k,116051718899658+c.lower,116052108545297+c.upper)) = pointBounds71372 := by
 decide +kernel
def cuts71373 : List PrefixCut := [⟨64,171038336,171038436⟩]
theorem checked71373 : checkPrefixCuts (2^48) 9358934017 10 Manual.Count131072.C071373.packed 64 cuts71373 = true := by
 decide +kernel
def cuts71374 : List PrefixCut := [⟨41,109833806,109833871⟩,
⟨64,170945721,170945825⟩]
theorem checked71374 : checkPrefixCuts (2^48) 9359065089 10 Manual.Count131072.C071374.packed 64 cuts71374 = true := by
 decide +kernel
def pointBounds71374 : List (Nat × Nat × Nat) := [(9359149056,116052173218583,116052562864486)]
theorem point_links_checked71374 : (cuts71374.take 1).map (fun c => (9359065089-1+2*2^10*c.k,116052063384777+c.lower,116052453030615+c.upper)) = pointBounds71374 := by
 decide +kernel
def cuts71375 : List PrefixCut := [⟨64,171364364,171364467⟩]
theorem checked71375 : checkPrefixCuts (2^48) 9359196161 10 Manual.Count131072.C071375.packed 64 cuts71375 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000042
