import PlattAssemblyKernel
import PlattCertificates.Count131072.C049280
import PlattCertificates.Count131072.C049281
import PlattCertificates.Count131072.C049282
import PlattCertificates.Count131072.C049283
import PlattCertificates.Count131072.C049284
import PlattCertificates.Count131072.C049285
import PlattCertificates.Count131072.C049286
import PlattCertificates.Count131072.C049287
import PlattCertificates.Count131072.C049288
import PlattCertificates.Count131072.C049289
import PlattCertificates.Count131072.C049290
import PlattCertificates.Count131072.C049291
import PlattCertificates.Count131072.C049292
import PlattCertificates.Count131072.C049293
import PlattCertificates.Count131072.C049294
import PlattCertificates.Count131072.C049295
import PlattCertificates.Count131072.C049296
import PlattCertificates.Count131072.C049297
import PlattCertificates.Count131072.C049298
import PlattCertificates.Count131072.C049299
import PlattCertificates.Count131072.C049300
import PlattCertificates.Count131072.C049301
import PlattCertificates.Count131072.C049302
import PlattCertificates.Count131072.C049303
import PlattCertificates.Count131072.C049304
import PlattCertificates.Count131072.C049305
import PlattCertificates.Count131072.C049306
import PlattCertificates.Count131072.C049307
import PlattCertificates.Count131072.C049308
import PlattCertificates.Count131072.C049309
import PlattCertificates.Count131072.C049310
import PlattCertificates.Count131072.C049311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000290
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49280 : List PrefixCut := [⟨64,256989839,256989989⟩]
theorem checked49280 : checkPrefixCuts (2^48) 6463160321 10 Manual.Count131072.C049280.packed 64 cuts49280 = true := by
 decide +kernel
def cuts49281 : List PrefixCut := [⟨33,128732470,128732540⟩,
⟨64,249102202,249102342⟩]
theorem checked49281 : checkPrefixCuts (2^48) 6463291393 10 Manual.Count131072.C049281.packed 64 cuts49281 = true := by
 decide +kernel
def pointBounds49281 : List (Nat × Nat × Nat) := [(6463358976,111476621447637,111477008467006)]
theorem point_links_checked49281 : (cuts49281.take 1).map (fun c => (6463291393-1+2*2^10*c.k,111476492715167+c.lower,111476879734466+c.upper)) = pointBounds49281 := by
 decide +kernel
def cuts49282 : List PrefixCut := [⟨64,256413312,256413458⟩]
theorem checked49282 : checkPrefixCuts (2^48) 6463422465 10 Manual.Count131072.C049282.packed 64 cuts49282 = true := by
 decide +kernel
def cuts49283 : List PrefixCut := [⟨4,16156302,16156311⟩,
⟨64,251530765,251530914⟩]
theorem checked49283 : checkPrefixCuts (2^48) 6463553537 10 Manual.Count131072.C049283.packed 64 cuts49283 = true := by
 decide +kernel
def pointBounds49283 : List (Nat × Nat × Nat) := [(6463561728,111477014386983,111477401406577)]
theorem point_links_checked49283 : (cuts49283.take 1).map (fun c => (6463553537-1+2*2^10*c.k,111476998230681+c.lower,111477385250266+c.upper)) = pointBounds49283 := by
 decide +kernel
def cuts49284 : List PrefixCut := [⟨39,155505842,155505928⟩,
⟨64,255227131,255227277⟩]
theorem checked49284 : checkPrefixCuts (2^48) 6463684609 10 Manual.Count131072.C049284.packed 64 cuts49284 = true := by
 decide +kernel
def pointBounds49284 : List (Nat × Nat × Nat) := [(6463764480,111477405267288,111477792287108)]
theorem point_links_checked49284 : (cuts49284.take 1).map (fun c => (6463684609-1+2*2^10*c.k,111477249761446+c.lower,111477636781180+c.upper)) = pointBounds49284 := by
 decide +kernel
def cuts49285 : List PrefixCut := [⟨64,254002665,254002809⟩]
theorem checked49285 : checkPrefixCuts (2^48) 6463815681 10 Manual.Count131072.C049285.packed 64 cuts49285 = true := by
 decide +kernel
def cuts49286 : List PrefixCut := [⟨10,41411573,41411596⟩,
⟨64,257002132,257002275⟩]
theorem checked49286 : checkPrefixCuts (2^48) 6463946753 10 Manual.Count131072.C049286.packed 64 cuts49286 = true := by
 decide +kernel
def pointBounds49286 : List (Nat × Nat × Nat) := [(6463967232,111477800402815,111478187422862)]
theorem point_links_checked49286 : (cuts49286.take 1).map (fun c => (6463946753-1+2*2^10*c.k,111477758991242+c.lower,111478146011266+c.upper)) = pointBounds49286 := by
 decide +kernel
def cuts49287 : List PrefixCut := [⟨45,180708305,180708406⟩,
⟨64,254297203,254297347⟩]
theorem checked49287 : checkPrefixCuts (2^48) 6464077825 10 Manual.Count131072.C049287.packed 64 cuts49287 = true := by
 decide +kernel
def pointBounds49287 : List (Nat × Nat × Nat) := [(6464169984,111478196701679,111478583721947)]
theorem point_links_checked49287 : (cuts49287.take 1).map (fun c => (6464077825-1+2*2^10*c.k,111478015993374+c.lower,111478403013541+c.upper)) = pointBounds49287 := by
 decide +kernel
def cuts49288 : List PrefixCut := [⟨64,249153920,249154059⟩]
theorem checked49288 : checkPrefixCuts (2^48) 6464208897 10 Manual.Count131072.C049288.packed 64 cuts49288 = true := by
 decide +kernel
def cuts49289 : List PrefixCut := [⟨16,64007622,64007657⟩,
⟨64,254591650,254591796⟩]
theorem checked49289 : checkPrefixCuts (2^48) 6464339969 10 Manual.Count131072.C049289.packed 64 cuts49289 = true := by
 decide +kernel
def pointBounds49289 : List (Nat × Nat × Nat) := [(6464372736,111478583452119,111478970472604)]
theorem point_links_checked49289 : (cuts49289.take 1).map (fun c => (6464339969-1+2*2^10*c.k,111478519444497+c.lower,111478906464947+c.upper)) = pointBounds49289 := by
 decide +kernel
def cuts49290 : List PrefixCut := [⟨51,198287887,198288000⟩,
⟨64,249187361,249187502⟩]
theorem checked49290 : checkPrefixCuts (2^48) 6464471041 10 Manual.Count131072.C049290.packed 64 cuts49290 = true := by
 decide +kernel
def pointBounds49290 : List (Nat × Nat × Nat) := [(6464575488,111478972324034,111479359344743)]
theorem point_links_checked49290 : (cuts49290.take 1).map (fun c => (6464471041-1+2*2^10*c.k,111478774036147+c.lower,111479161056743+c.upper)) = pointBounds49290 := by
 decide +kernel
def cuts49291 : List PrefixCut := [⟨64,254755496,254755644⟩]
theorem checked49291 : checkPrefixCuts (2^48) 6464602113 10 Manual.Count131072.C049291.packed 64 cuts49291 = true := by
 decide +kernel
def cuts49292 : List PrefixCut := [⟨22,87602299,87602348⟩,
⟨64,249873908,249874049⟩]
theorem checked49292 : checkPrefixCuts (2^48) 6464733185 10 Manual.Count131072.C049292.packed 64 cuts49292 = true := by
 decide +kernel
def pointBounds49292 : List (Nat × Nat × Nat) := [(6464778240,111479365581303,111479752602237)]
theorem point_links_checked49292 : (cuts49292.take 1).map (fun c => (6464733185-1+2*2^10*c.k,111479277979004+c.lower,111479664999889+c.upper)) = pointBounds49292 := by
 decide +kernel
def cuts49293 : List PrefixCut := [⟨57,226619382,226619509⟩,
⟨64,253830849,253830991⟩]
theorem checked49293 : checkPrefixCuts (2^48) 6464864257 10 Manual.Count131072.C049293.packed 64 cuts49293 = true := by
 decide +kernel
def pointBounds49293 : List (Nat × Nat × Nat) := [(6464980992,111479754472294,111480141493447)]
theorem point_links_checked49293 : (cuts49293.take 1).map (fun c => (6464864257-1+2*2^10*c.k,111479527852912+c.lower,111479914873938+c.upper)) = pointBounds49293 := by
 decide +kernel
def cuts49294 : List PrefixCut := [⟨64,253042017,253042161⟩]
theorem checked49294 : checkPrefixCuts (2^48) 6464995329 10 Manual.Count131072.C049294.packed 64 cuts49294 = true := by
 decide +kernel
def cuts49295 : List PrefixCut := [⟨28,109844412,109844475⟩,
⟨64,252209679,252209824⟩]
theorem checked49295 : checkPrefixCuts (2^48) 6465126401 10 Manual.Count131072.C049295.packed 64 cuts49295 = true := by
 decide +kernel
def pointBounds49295 : List (Nat × Nat × Nat) := [(6465183744,111480144570190,111480531591565)]
theorem point_links_checked49295 : (cuts49295.take 1).map (fun c => (6465126401-1+2*2^10*c.k,111480034725778+c.lower,111480421747090+c.upper)) = pointBounds49295 := by
 decide +kernel
def cuts49296 : List PrefixCut := [⟨63,244934092,244934231⟩,
⟨64,248895837,248895978⟩]
theorem checked49296 : checkPrefixCuts (2^48) 6465257473 10 Manual.Count131072.C049296.packed 64 cuts49296 = true := by
 decide +kernel
def pointBounds49296 : List (Nat × Nat × Nat) := [(6465386496,111480531869549,111480918891145)]
theorem point_links_checked49296 : (cuts49296.take 1).map (fun c => (6465257473-1+2*2^10*c.k,111480286935457+c.lower,111480673956914+c.upper)) = pointBounds49296 := by
 decide +kernel
def cuts49297 : List PrefixCut := [⟨64,251894702,251894845⟩]
theorem checked49297 : checkPrefixCuts (2^48) 6465388545 10 Manual.Count131072.C049297.packed 64 cuts49297 = true := by
 decide +kernel
def cuts49298 : List PrefixCut := [⟨34,131953167,131953240⟩,
⟨64,247927985,247928125⟩]
theorem checked49298 : checkPrefixCuts (2^48) 6465519617 10 Manual.Count131072.C049298.packed 64 cuts49298 = true := by
 decide +kernel
def pointBounds49298 : List (Nat × Nat × Nat) := [(6465589248,111480919679163,111481306700977)]
theorem point_links_checked49298 : (cuts49298.take 1).map (fun c => (6465519617-1+2*2^10*c.k,111480787725996+c.lower,111481174747737+c.upper)) = pointBounds49298 := by
 decide +kernel
def cuts49299 : List PrefixCut := [⟨64,251057391,251057538⟩]
theorem checked49299 : checkPrefixCuts (2^48) 6465650689 10 Manual.Count131072.C049299.packed 64 cuts49299 = true := by
 decide +kernel
def cuts49300 : List PrefixCut := [⟨5,20112232,20112243⟩,
⟨64,253838360,253838511⟩]
theorem checked49300 : checkPrefixCuts (2^48) 6465781761 10 Manual.Count131072.C049300.packed 64 cuts49300 = true := by
 decide +kernel
def pointBounds49300 : List (Nat × Nat × Nat) := [(6465792000,111481306823604,111481693845643)]
theorem point_links_checked49300 : (cuts49300.take 1).map (fun c => (6465781761-1+2*2^10*c.k,111481286711372+c.lower,111481673733400+c.upper)) = pointBounds49300 := by
 decide +kernel
def cuts49301 : List PrefixCut := [⟨40,158630046,158630140⟩,
⟨64,253702633,253702781⟩]
theorem checked49301 : checkPrefixCuts (2^48) 6465912833 10 Manual.Count131072.C049301.packed 64 cuts49301 = true := by
 decide +kernel
def pointBounds49301 : List (Nat × Nat × Nat) := [(6465994752,111481699179778,111482086202051)]
theorem point_links_checked49301 : (cuts49301.take 1).map (fun c => (6465912833-1+2*2^10*c.k,111481540549732+c.lower,111481927571911+c.upper)) = pointBounds49301 := by
 decide +kernel
def cuts49302 : List PrefixCut := [⟨64,254742208,254742353⟩]
theorem checked49302 : checkPrefixCuts (2^48) 6466043905 10 Manual.Count131072.C049302.packed 64 cuts49302 = true := by
 decide +kernel
def cuts49303 : List PrefixCut := [⟨11,44183232,44183259⟩,
⟨64,251559373,251559520⟩]
theorem checked49303 : checkPrefixCuts (2^48) 6466174977 10 Manual.Count131072.C049303.packed 64 cuts49303 = true := by
 decide +kernel
def pointBounds49303 : List (Nat × Nat × Nat) := [(6466197504,111482093177805,111482480200304)]
theorem point_links_checked49303 : (cuts49303.take 1).map (fun c => (6466174977-1+2*2^10*c.k,111482048994573+c.lower,111482436017045+c.upper)) = pointBounds49303 := by
 decide +kernel
def cuts49304 : List PrefixCut := [⟨46,182735399,182735505⟩,
⟨64,252903684,252903832⟩]
theorem checked49304 : checkPrefixCuts (2^48) 6466306049 10 Manual.Count131072.C049304.packed 64 cuts49304 = true := by
 decide +kernel
def pointBounds49304 : List (Nat × Nat × Nat) := [(6466400256,111482483289345,111482870312070)]
theorem point_links_checked49304 : (cuts49304.take 1).map (fun c => (6466306049-1+2*2^10*c.k,111482300553946+c.lower,111482687576565+c.upper)) = pointBounds49304 := by
 decide +kernel
def cuts49305 : List PrefixCut := [⟨64,251462136,251462282⟩]
theorem checked49305 : checkPrefixCuts (2^48) 6466437121 10 Manual.Count131072.C049305.packed 64 cuts49305 = true := by
 decide +kernel
def cuts49306 : List PrefixCut := [⟨17,65334916,65334953⟩,
⟨64,250760565,250760710⟩]
theorem checked49306 : checkPrefixCuts (2^48) 6466568193 10 Manual.Count131072.C049306.packed 64 cuts49306 = true := by
 decide +kernel
def pointBounds49306 : List (Nat × Nat × Nat) := [(6466603008,111482870254682,111483257277632)]
theorem point_links_checked49306 : (cuts49306.take 1).map (fun c => (6466568193-1+2*2^10*c.k,111482804919766+c.lower,111483191942679+c.upper)) = pointBounds49306 := by
 decide +kernel
def cuts49307 : List PrefixCut := [⟨52,206054300,206054422⟩,
⟨64,253367093,253367243⟩]
theorem checked49307 : checkPrefixCuts (2^48) 6466699265 10 Manual.Count131072.C049307.packed 64 cuts49307 = true := by
 decide +kernel
def pointBounds49307 : List (Nat × Nat × Nat) := [(6466805760,111483261734631,111483648757811)]
theorem point_links_checked49307 : (cuts49307.take 1).map (fun c => (6466699265-1+2*2^10*c.k,111483055680331+c.lower,111483442703389+c.upper)) = pointBounds49307 := by
 decide +kernel
def cuts49308 : List PrefixCut := [⟨64,250271622,250271766⟩]
theorem checked49308 : checkPrefixCuts (2^48) 6466830337 10 Manual.Count131072.C049308.packed 64 cuts49308 = true := by
 decide +kernel
def cuts49309 : List PrefixCut := [⟨23,89791884,89791936⟩,
⟨64,251224115,251224257⟩]
theorem checked49309 : checkPrefixCuts (2^48) 6466961409 10 Manual.Count131072.C049309.packed 64 cuts49309 = true := by
 decide +kernel
def pointBounds49309 : List (Nat × Nat × Nat) := [(6467008512,111483649110930,111484036134334)]
theorem point_links_checked49309 : (cuts49309.take 1).map (fun c => (6466961409-1+2*2^10*c.k,111483559319046+c.lower,111483946342398+c.upper)) = pointBounds49309 := by
 decide +kernel
def cuts49310 : List PrefixCut := [⟨58,229587933,229588067⟩,
⟨64,254396237,254396383⟩]
theorem checked49310 : checkPrefixCuts (2^48) 6467092481 10 Manual.Count131072.C049310.packed 64 cuts49310 = true := by
 decide +kernel
def pointBounds49310 : List (Nat × Nat × Nat) := [(6467211264,111484040131094,111484427154722)]
theorem point_links_checked49310 : (cuts49310.take 1).map (fun c => (6467092481-1+2*2^10*c.k,111483810543161+c.lower,111484197566655+c.upper)) = pointBounds49310 := by
 decide +kernel
def cuts49311 : List PrefixCut := [⟨64,251823251,251823396⟩]
theorem checked49311 : checkPrefixCuts (2^48) 6467223553 10 Manual.Count131072.C049311.packed 64 cuts49311 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000290
