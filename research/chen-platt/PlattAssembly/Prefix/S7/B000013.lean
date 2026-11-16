import PlattAssemblyKernel
import PlattCertificates.Count131072.C060416
import PlattCertificates.Count131072.C060417
import PlattCertificates.Count131072.C060418
import PlattCertificates.Count131072.C060419
import PlattCertificates.Count131072.C060420
import PlattCertificates.Count131072.C060421
import PlattCertificates.Count131072.C060422
import PlattCertificates.Count131072.C060423
import PlattCertificates.Count131072.C060424
import PlattCertificates.Count131072.C060425
import PlattCertificates.Count131072.C060426
import PlattCertificates.Count131072.C060427
import PlattCertificates.Count131072.C060428
import PlattCertificates.Count131072.C060429
import PlattCertificates.Count131072.C060430
import PlattCertificates.Count131072.C060431
import PlattCertificates.Count131072.C060432
import PlattCertificates.Count131072.C060433
import PlattCertificates.Count131072.C060434
import PlattCertificates.Count131072.C060435
import PlattCertificates.Count131072.C060436
import PlattCertificates.Count131072.C060437
import PlattCertificates.Count131072.C060438
import PlattCertificates.Count131072.C060439
import PlattCertificates.Count131072.C060440
import PlattCertificates.Count131072.C060441
import PlattCertificates.Count131072.C060442
import PlattCertificates.Count131072.C060443
import PlattCertificates.Count131072.C060444
import PlattCertificates.Count131072.C060445
import PlattCertificates.Count131072.C060446
import PlattCertificates.Count131072.C060447
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60416 : List PrefixCut := [⟨51,161719193,161719288⟩,
⟨64,201651282,201651400⟩]
theorem checked60416 : checkPrefixCuts (2^48) 7922778113 10 Manual.Count131072.C060416.packed 64 cuts60416 = true := by
 decide +kernel
def pointBounds60416 : List (Nat × Nat × Nat) := [(7922882560,114002254905398,114002643361431)]
theorem point_links_checked60416 : (cuts60416.take 1).map (fun c => (7922778113-1+2*2^10*c.k,114002093186205+c.lower,114002481642143+c.upper)) = pointBounds60416 := by
 decide +kernel
def cuts60417 : List PrefixCut := [⟨64,205946643,205946759⟩]
theorem checked60417 : checkPrefixCuts (2^48) 7922909185 10 Manual.Count131072.C060417.packed 64 cuts60417 = true := by
 decide +kernel
def cuts60418 : List PrefixCut := [⟨44,140505000,140505084⟩,
⟨64,204415602,204415723⟩]
theorem checked60418 : checkPrefixCuts (2^48) 7923040257 10 Manual.Count131072.C060418.packed 64 cuts60418 = true := by
 decide +kernel
def pointBounds60418 : List (Nat × Nat × Nat) := [(7923130368,114002641289130,114003029745386)]
theorem point_links_checked60418 : (cuts60418.take 1).map (fun c => (7923040257-1+2*2^10*c.k,114002500784130+c.lower,114002889240302+c.upper)) = pointBounds60418 := by
 decide +kernel
def cuts60419 : List PrefixCut := [⟨64,201641266,201641379⟩]
theorem checked60419 : checkPrefixCuts (2^48) 7923171329 10 Manual.Count131072.C060419.packed 64 cuts60419 = true := by
 decide +kernel
def cuts60420 : List PrefixCut := [⟨37,119185622,119185686⟩,
⟨64,206291656,206291768⟩]
theorem checked60420 : checkPrefixCuts (2^48) 7923302401 10 Manual.Count131072.C060420.packed 64 cuts60420 = true := by
 decide +kernel
def pointBounds60420 : List (Nat × Nat × Nat) := [(7923378176,114003026026620,114003414483090)]
theorem point_links_checked60420 : (cuts60420.take 1).map (fun c => (7923302401-1+2*2^10*c.k,114002906840998+c.lower,114003295297404+c.upper)) = pointBounds60420 := by
 decide +kernel
def cuts60421 : List PrefixCut := [⟨64,203162128,203162248⟩]
theorem checked60421 : checkPrefixCuts (2^48) 7923433473 10 Manual.Count131072.C060421.packed 64 cuts60421 = true := by
 decide +kernel
def cuts60422 : List PrefixCut := [⟨30,96482193,96482246⟩,
⟨64,204686288,204686408⟩]
theorem checked60422 : checkPrefixCuts (2^48) 7923564545 10 Manual.Count131072.C060422.packed 64 cuts60422 = true := by
 decide +kernel
def pointBounds60422 : List (Nat × Nat × Nat) := [(7923625984,114003412776975,114003801233666)]
theorem point_links_checked60422 : (cuts60422.take 1).map (fun c => (7923564545-1+2*2^10*c.k,114003316294782+c.lower,114003704751420+c.upper)) = pointBounds60422 := by
 decide +kernel
def cuts60423 : List PrefixCut := [⟨64,205713063,205713184⟩]
theorem checked60423 : checkPrefixCuts (2^48) 7923695617 10 Manual.Count131072.C060423.packed 64 cuts60423 = true := by
 decide +kernel
def cuts60424 : List PrefixCut := [⟨23,73993343,73993388⟩,
⟨64,204004581,204004699⟩]
theorem checked60424 : checkPrefixCuts (2^48) 7923826689 10 Manual.Count131072.C060424.packed 64 cuts60424 = true := by
 decide +kernel
def pointBounds60424 : List (Nat × Nat × Nat) := [(7923873792,114003800687476,114004189144400)]
theorem point_links_checked60424 : (cuts60424.take 1).map (fun c => (7923826689-1+2*2^10*c.k,114003726694133+c.lower,114004115151012+c.upper)) = pointBounds60424 := by
 decide +kernel
def cuts60425 : List PrefixCut := [⟨64,203255271,203255388⟩]
theorem checked60425 : checkPrefixCuts (2^48) 7923957761 10 Manual.Count131072.C060425.packed 64 cuts60425 = true := by
 decide +kernel
def cuts60426 : List PrefixCut := [⟨16,52322945,52322975⟩,
⟨64,207585472,207585594⟩]
theorem checked60426 : checkPrefixCuts (2^48) 7924088833 10 Manual.Count131072.C060426.packed 64 cuts60426 = true := by
 decide +kernel
def pointBounds60426 : List (Nat × Nat × Nat) := [(7924121600,114004186276930,114004574734074)]
theorem point_links_checked60426 : (cuts60426.take 1).map (fun c => (7924088833-1+2*2^10*c.k,114004133953985+c.lower,114004522411099+c.upper)) = pointBounds60426 := by
 decide +kernel
def cuts60427 : List PrefixCut := [⟨64,200975209,200975329⟩]
theorem checked60427 : checkPrefixCuts (2^48) 7924219905 10 Manual.Count131072.C060427.packed 64 cuts60427 = true := by
 decide +kernel
def cuts60428 : List PrefixCut := [⟨9,28771365,28771383⟩,
⟨64,202392702,202392820⟩]
theorem checked60428 : checkPrefixCuts (2^48) 7924350977 10 Manual.Count131072.C060428.packed 64 cuts60428 = true := by
 decide +kernel
def pointBounds60428 : List (Nat × Nat × Nat) := [(7924369408,114004571286031,114004959743405)]
theorem point_links_checked60428 : (cuts60428.take 1).map (fun c => (7924350977-1+2*2^10*c.k,114004542514666+c.lower,114004930972022+c.upper)) = pointBounds60428 := by
 decide +kernel
def cuts60429 : List PrefixCut := [⟨64,206154404,206154520⟩]
theorem checked60429 : checkPrefixCuts (2^48) 7924482049 10 Manual.Count131072.C060429.packed 64 cuts60429 = true := by
 decide +kernel
def cuts60430 : List PrefixCut := [⟨2,6997255,6997259⟩,
⟨64,202492545,202492661⟩]
theorem checked60430 : checkPrefixCuts (2^48) 7924613121 10 Manual.Count131072.C060430.packed 64 cuts60430 = true := by
 decide +kernel
def pointBounds60430 : List (Nat × Nat × Nat) := [(7924617216,114004958059027,114005346516621)]
theorem point_links_checked60430 : (cuts60430.take 1).map (fun c => (7924613121-1+2*2^10*c.k,114004951061772+c.lower,114005339519362+c.upper)) = pointBounds60430 := by
 decide +kernel
def cuts60431 : List PrefixCut := [⟨59,186967874,186967980⟩,
⟨64,201032970,201033085⟩]
theorem checked60431 : checkPrefixCuts (2^48) 7924744193 10 Manual.Count131072.C060431.packed 64 cuts60431 = true := by
 decide +kernel
def pointBounds60431 : List (Nat × Nat × Nat) := [(7924865024,114005340522191,114005728980003)]
theorem point_links_checked60431 : (cuts60431.take 1).map (fun c => (7924744193-1+2*2^10*c.k,114005153554317+c.lower,114005542012023+c.upper)) = pointBounds60431 := by
 decide +kernel
def cuts60432 : List PrefixCut := [⟨64,204758985,204759097⟩]
theorem checked60432 : checkPrefixCuts (2^48) 7924875265 10 Manual.Count131072.C060432.packed 64 cuts60432 = true := by
 decide +kernel
def cuts60433 : List PrefixCut := [⟨52,165118863,165118955⟩,
⟨64,204862137,204862253⟩]
theorem checked60433 : checkPrefixCuts (2^48) 7925006337 10 Manual.Count131072.C060433.packed 64 cuts60433 = true := by
 decide +kernel
def pointBounds60433 : List (Nat × Nat × Nat) := [(7925112832,114005724465135,114006112923160)]
theorem point_links_checked60433 : (cuts60433.take 1).map (fun c => (7925006337-1+2*2^10*c.k,114005559346272+c.lower,114005947804205+c.upper)) = pointBounds60433 := by
 decide +kernel
def cuts60434 : List PrefixCut := [⟨64,203402584,203402702⟩]
theorem checked60434 : checkPrefixCuts (2^48) 7925137409 10 Manual.Count131072.C060434.packed 64 cuts60434 = true := by
 decide +kernel
def cuts60435 : List PrefixCut := [⟨45,141957161,141957247⟩,
⟨64,201978580,201978701⟩]
theorem checked60435 : checkPrefixCuts (2^48) 7925268481 10 Manual.Count131072.C060435.packed 64 cuts60435 = true := by
 decide +kernel
def pointBounds60435 : List (Nat × Nat × Nat) := [(7925360640,114006109568154,114006498026407)]
theorem point_links_checked60435 : (cuts60435.take 1).map (fun c => (7925268481-1+2*2^10*c.k,114005967610993+c.lower,114006356069160+c.upper)) = pointBounds60435 := by
 decide +kernel
def cuts60436 : List PrefixCut := [⟨64,204709935,204710055⟩]
theorem checked60436 : checkPrefixCuts (2^48) 7925399553 10 Manual.Count131072.C060436.packed 64 cuts60436 = true := by
 decide +kernel
def cuts60437 : List PrefixCut := [⟨38,118122177,118122246⟩,
⟨64,200480283,200480397⟩]
theorem checked60437 : checkPrefixCuts (2^48) 7925530625 10 Manual.Count131072.C060437.packed 64 cuts60437 = true := by
 decide +kernel
def pointBounds60437 : List (Nat × Nat × Nat) := [(7925608448,114006492421685,114006880880162)]
theorem point_links_checked60437 : (cuts60437.take 1).map (fun c => (7925530625-1+2*2^10*c.k,114006374299508+c.lower,114006762757916+c.upper)) = pointBounds60437 := by
 decide +kernel
def cuts60438 : List PrefixCut := [⟨64,207508745,207508868⟩]
theorem checked60438 : checkPrefixCuts (2^48) 7925661697 10 Manual.Count131072.C060438.packed 64 cuts60438 = true := by
 decide +kernel
def cuts60439 : List PrefixCut := [⟨31,99225117,99225173⟩,
⟨64,204309116,204309233⟩]
theorem checked60439 : checkPrefixCuts (2^48) 7925792769 10 Manual.Count131072.C060439.packed 64 cuts60439 = true := by
 decide +kernel
def pointBounds60439 : List (Nat × Nat × Nat) := [(7925856256,114006881513653,114007269972354)]
theorem point_links_checked60439 : (cuts60439.take 1).map (fun c => (7925792769-1+2*2^10*c.k,114006782288536+c.lower,114007170747181+c.upper)) = pointBounds60439 := by
 decide +kernel
def cuts60440 : List PrefixCut := [⟨64,204660875,204660991⟩]
theorem checked60440 : checkPrefixCuts (2^48) 7925923841 10 Manual.Count131072.C060440.packed 64 cuts60440 = true := by
 decide +kernel
def cuts60441 : List PrefixCut := [⟨24,76209826,76209868⟩,
⟨64,203911715,203911831⟩]
theorem checked60441 : checkPrefixCuts (2^48) 7926054913 10 Manual.Count131072.C060441.packed 64 cuts60441 = true := by
 decide +kernel
def pointBounds60441 : List (Nat × Nat × Nat) := [(7926104064,114007267468353,114007655927273)]
theorem point_links_checked60441 : (cuts60441.take 1).map (fun c => (7926054913-1+2*2^10*c.k,114007191258527+c.lower,114007579717405+c.upper)) = pointBounds60441 := by
 decide +kernel
def cuts60442 : List PrefixCut := [⟨64,206607241,206607356⟩]
theorem checked60442 : checkPrefixCuts (2^48) 7926185985 10 Manual.Count131072.C060442.packed 64 cuts60442 = true := by
 decide +kernel
def cuts60443 : List PrefixCut := [⟨17,53622149,53622180⟩,
⟨64,199785691,199785806⟩]
theorem checked60443 : checkPrefixCuts (2^48) 7926317057 10 Manual.Count131072.C060443.packed 64 cuts60443 = true := by
 decide +kernel
def pointBounds60443 : List (Nat × Nat × Nat) := [(7926351872,114007655399632,114008043858772)]
theorem point_links_checked60443 : (cuts60443.take 1).map (fun c => (7926317057-1+2*2^10*c.k,114007601777483+c.lower,114007990236592+c.upper)) = pointBounds60443 := by
 decide +kernel
def cuts60444 : List PrefixCut := [⟨64,203724050,203724166⟩]
theorem checked60444 : checkPrefixCuts (2^48) 7926448129 10 Manual.Count131072.C060444.packed 64 cuts60444 = true := by
 decide +kernel
def cuts60445 : List PrefixCut := [⟨10,31888172,31888191⟩,
⟨64,203294572,203294680⟩]
theorem checked60445 : checkPrefixCuts (2^48) 7926579201 10 Manual.Count131072.C060445.packed 64 cuts60445 = true := by
 decide +kernel
def pointBounds60445 : List (Nat × Nat × Nat) := [(7926599680,114008037175396,114008425634755)]
theorem point_links_checked60445 : (cuts60445.take 1).map (fun c => (7926579201-1+2*2^10*c.k,114008005287224+c.lower,114008393746564+c.upper)) = pointBounds60445 := by
 decide +kernel
def cuts60446 : List PrefixCut := [⟨64,204178936,204179053⟩]
theorem checked60446 : checkPrefixCuts (2^48) 7926710273 10 Manual.Count131072.C060446.packed 64 cuts60446 = true := by
 decide +kernel
def cuts60447 : List PrefixCut := [⟨3,9516431,9516437⟩,
⟨64,205311844,205311966⟩]
theorem checked60447 : checkPrefixCuts (2^48) 7926841345 10 Manual.Count131072.C060447.packed 64 cuts60447 = true := by
 decide +kernel
def pointBounds60447 : List (Nat × Nat × Nat) := [(7926847488,114008422277163,114008810736734)]
theorem point_links_checked60447 : (cuts60447.take 1).map (fun c => (7926841345-1+2*2^10*c.k,114008412760732+c.lower,114008801220297+c.upper)) = pointBounds60447 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000013
