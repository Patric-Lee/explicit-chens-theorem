import PlattAssemblyKernel
import PlattCertificates.Count131072.C063392
import PlattCertificates.Count131072.C063393
import PlattCertificates.Count131072.C063394
import PlattCertificates.Count131072.C063395
import PlattCertificates.Count131072.C063396
import PlattCertificates.Count131072.C063397
import PlattCertificates.Count131072.C063398
import PlattCertificates.Count131072.C063399
import PlattCertificates.Count131072.C063400
import PlattCertificates.Count131072.C063401
import PlattCertificates.Count131072.C063402
import PlattCertificates.Count131072.C063403
import PlattCertificates.Count131072.C063404
import PlattCertificates.Count131072.C063405
import PlattCertificates.Count131072.C063406
import PlattCertificates.Count131072.C063407
import PlattCertificates.Count131072.C063408
import PlattCertificates.Count131072.C063409
import PlattCertificates.Count131072.C063410
import PlattCertificates.Count131072.C063411
import PlattCertificates.Count131072.C063412
import PlattCertificates.Count131072.C063413
import PlattCertificates.Count131072.C063414
import PlattCertificates.Count131072.C063415
import PlattCertificates.Count131072.C063416
import PlattCertificates.Count131072.C063417
import PlattCertificates.Count131072.C063418
import PlattCertificates.Count131072.C063419
import PlattCertificates.Count131072.C063420
import PlattCertificates.Count131072.C063421
import PlattCertificates.Count131072.C063422
import PlattCertificates.Count131072.C063423
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000106
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63392 : List PrefixCut := [⟨64,194864039,194864150⟩]
theorem checked63392 : checkPrefixCuts (2^48) 8312848385 10 Manual.Count131072.C063392.packed 64 cuts63392 = true := by
 decide +kernel
def cuts63393 : List PrefixCut := [⟨23,69073566,69073607⟩,
⟨64,193472728,193472839⟩]
theorem checked63393 : checkPrefixCuts (2^48) 8312979457 10 Manual.Count131072.C063393.packed 64 cuts63393 = true := by
 decide +kernel
def pointBounds63393 : List (Nat × Nat × Nat) := [(8313026560,114595318624546,114595707420824)]
theorem point_links_checked63393 : (cuts63393.take 1).map (fun c => (8312979457-1+2*2^10*c.k,114595249550980+c.lower,114595638347217+c.upper)) = pointBounds63393 := by
 decide +kernel
def cuts63394 : List PrefixCut := [⟨64,194180715,194180824⟩]
theorem checked63394 : checkPrefixCuts (2^48) 8313110529 10 Manual.Count131072.C063394.packed 64 cuts63394 = true := by
 decide +kernel
def cuts63395 : List PrefixCut := [⟨22,65448537,65448573⟩,
⟨64,193635928,193636036⟩]
theorem checked63395 : checkPrefixCuts (2^48) 8313241601 10 Manual.Count131072.C063395.packed 64 cuts63395 = true := by
 decide +kernel
def pointBounds63395 : List (Nat × Nat × Nat) := [(8313286656,114595702652960,114596091449453)]
theorem point_links_checked63395 : (cuts63395.take 1).map (fun c => (8313241601-1+2*2^10*c.k,114595637204423+c.lower,114596026000880+c.upper)) = pointBounds63395 := by
 decide +kernel
def cuts63396 : List PrefixCut := [⟨64,192346266,192346381⟩]
theorem checked63396 : checkPrefixCuts (2^48) 8313372673 10 Manual.Count131072.C063396.packed 64 cuts63396 = true := by
 decide +kernel
def cuts63397 : List PrefixCut := [⟨21,65717341,65717379⟩,
⟨64,195965990,195966105⟩]
theorem checked63397 : checkPrefixCuts (2^48) 8313503745 10 Manual.Count131072.C063397.packed 64 cuts63397 = true := by
 decide +kernel
def pointBounds63397 : List (Nat × Nat × Nat) := [(8313546752,114596088903958,114596477700676)]
theorem point_links_checked63397 : (cuts63397.take 1).map (fun c => (8313503745-1+2*2^10*c.k,114596023186617+c.lower,114596411983297+c.upper)) = pointBounds63397 := by
 decide +kernel
def cuts63398 : List PrefixCut := [⟨64,195150331,195150440⟩]
theorem checked63398 : checkPrefixCuts (2^48) 8313634817 10 Manual.Count131072.C063398.packed 64 cuts63398 = true := by
 decide +kernel
def cuts63399 : List PrefixCut := [⟨20,60365970,60366000⟩,
⟨64,197009339,197009449⟩]
theorem checked63399 : checkPrefixCuts (2^48) 8313765889 10 Manual.Count131072.C063399.packed 64 cuts63399 = true := by
 decide +kernel
def pointBounds63399 : List (Nat × Nat × Nat) := [(8313806848,114596474668908,114596863465842)]
theorem point_links_checked63399 : (cuts63399.take 1).map (fun c => (8313765889-1+2*2^10*c.k,114596414302938+c.lower,114596803099842+c.upper)) = pointBounds63399 := by
 decide +kernel
def cuts63400 : List PrefixCut := [⟨64,193552932,193553041⟩]
theorem checked63400 : checkPrefixCuts (2^48) 8313896961 10 Manual.Count131072.C063400.packed 64 cuts63400 = true := by
 decide +kernel
def cuts63401 : List PrefixCut := [⟨19,57181665,57181700⟩,
⟨64,194226995,194227110⟩]
theorem checked63401 : checkPrefixCuts (2^48) 8314028033 10 Manual.Count131072.C063401.packed 64 cuts63401 = true := by
 decide +kernel
def pointBounds63401 : List (Nat × Nat × Nat) := [(8314066944,114596862046874,114597250844032)]
theorem point_links_checked63401 : (cuts63401.take 1).map (fun c => (8314028033-1+2*2^10*c.k,114596804865209+c.lower,114597193662332+c.upper)) = pointBounds63401 := by
 decide +kernel
def cuts63402 : List PrefixCut := [⟨64,193039025,193039134⟩]
theorem checked63402 : checkPrefixCuts (2^48) 8314159105 10 Manual.Count131072.C063402.packed 64 cuts63402 = true := by
 decide +kernel
def cuts63403 : List PrefixCut := [⟨18,53422045,53422078⟩,
⟨64,190869317,190869430⟩]
theorem checked63403 : checkPrefixCuts (2^48) 8314290177 10 Manual.Count131072.C063403.packed 64 cuts63403 = true := by
 decide +kernel
def pointBounds63403 : List (Nat × Nat × Nat) := [(8314327040,114597245553274,114597634350654)]
theorem point_links_checked63403 : (cuts63403.take 1).map (fun c => (8314290177-1+2*2^10*c.k,114597192131229+c.lower,114597580928576+c.upper)) = pointBounds63403 := by
 decide +kernel
def cuts63404 : List PrefixCut := [⟨64,190358514,190358628⟩]
theorem checked63404 : checkPrefixCuts (2^48) 8314421249 10 Manual.Count131072.C063404.packed 64 cuts63404 = true := by
 decide +kernel
def cuts63405 : List PrefixCut := [⟨17,51423031,51423058⟩,
⟨64,193740808,193740920⟩]
theorem checked63405 : checkPrefixCuts (2^48) 8314552321 10 Manual.Count131072.C063405.packed 64 cuts63405 = true := by
 decide +kernel
def pointBounds63405 : List (Nat × Nat × Nat) := [(8314587136,114597624782091,114598013579692)]
theorem point_links_checked63405 : (cuts63405.take 1).map (fun c => (8314552321-1+2*2^10*c.k,114597573359060+c.lower,114597962156634+c.upper)) = pointBounds63405 := by
 decide +kernel
def cuts63406 : List PrefixCut := [⟨64,193229977,193230091⟩]
theorem checked63406 : checkPrefixCuts (2^48) 8314683393 10 Manual.Count131072.C063406.packed 64 cuts63406 = true := by
 decide +kernel
def cuts63407 : List PrefixCut := [⟨16,48780948,48780976⟩,
⟨64,195664269,195664378⟩]
theorem checked63407 : checkPrefixCuts (2^48) 8314814465 10 Manual.Count131072.C063407.packed 64 cuts63407 = true := by
 decide +kernel
def pointBounds63407 : List (Nat × Nat × Nat) := [(8314847232,114598009110793,114598397908621)]
theorem point_links_checked63407 : (cuts63407.take 1).map (fun c => (8314814465-1+2*2^10*c.k,114597960329845+c.lower,114598349127645+c.upper)) = pointBounds63407 := by
 decide +kernel
def cuts63408 : List PrefixCut := [⟨64,190448073,190448178⟩]
theorem checked63408 : checkPrefixCuts (2^48) 8314945537 10 Manual.Count131072.C063408.packed 64 cuts63408 = true := by
 decide +kernel
def cuts63409 : List PrefixCut := [⟨15,44852690,44852715⟩,
⟨64,193999398,193999512⟩]
theorem checked63409 : checkPrefixCuts (2^48) 8315076609 10 Manual.Count131072.C063409.packed 64 cuts63409 = true := by
 decide +kernel
def pointBounds63409 : List (Nat × Nat × Nat) := [(8315107328,114598391294877,114598780092916)]
theorem point_links_checked63409 : (cuts63409.take 1).map (fun c => (8315076609-1+2*2^10*c.k,114598346442187+c.lower,114598735240201+c.upper)) = pointBounds63409 := by
 decide +kernel
def cuts63410 : List PrefixCut := [⟨64,195147256,195147363⟩]
theorem checked63410 : checkPrefixCuts (2^48) 8315207681 10 Manual.Count131072.C063410.packed 64 cuts63410 = true := by
 decide +kernel
def cuts63411 : List PrefixCut := [⟨14,44343529,44343556⟩,
⟨64,194873390,194873499⟩]
theorem checked63411 : checkPrefixCuts (2^48) 8315338753 10 Manual.Count131072.C063411.packed 64 cuts63411 = true := by
 decide +kernel
def pointBounds63411 : List (Nat × Nat × Nat) := [(8315367424,114598779932370,114599168730632)]
theorem point_links_checked63411 : (cuts63411.take 1).map (fun c => (8315338753-1+2*2^10*c.k,114598735588841+c.lower,114599124387076+c.upper)) = pointBounds63411 := by
 decide +kernel
def cuts63412 : List PrefixCut := [⟨64,189792924,189793033⟩]
theorem checked63412 : checkPrefixCuts (2^48) 8315469825 10 Manual.Count131072.C063412.packed 64 cuts63412 = true := by
 decide +kernel
def cuts63413 : List PrefixCut := [⟨13,39907923,39907946⟩,
⟨64,195104175,195104287⟩]
theorem checked63413 : checkPrefixCuts (2^48) 8315600897 10 Manual.Count131072.C063413.packed 64 cuts63413 = true := by
 decide +kernel
def pointBounds63413 : List (Nat × Nat × Nat) := [(8315627520,114599160163078,114599548961554)]
theorem point_links_checked63413 : (cuts63413.take 1).map (fun c => (8315600897-1+2*2^10*c.k,114599120255155+c.lower,114599509053608+c.upper)) = pointBounds63413 := by
 decide +kernel
def cuts63414 : List PrefixCut := [⟨64,194017965,194018081⟩]
theorem checked63414 : checkPrefixCuts (2^48) 8315731969 10 Manual.Count131072.C063414.packed 64 cuts63414 = true := by
 decide +kernel
def cuts63415 : List PrefixCut := [⟨12,36623426,36623446⟩,
⟨64,193744132,193744243⟩]
theorem checked63415 : checkPrefixCuts (2^48) 8315863041 10 Manual.Count131072.C063415.packed 64 cuts63415 = true := by
 decide +kernel
def pointBounds63415 : List (Nat × Nat × Nat) := [(8315887616,114599546000721,114599934799422)]
theorem point_links_checked63415 : (cuts63415.take 1).map (fun c => (8315863041-1+2*2^10*c.k,114599509377295+c.lower,114599898175976+c.upper)) = pointBounds63415 := by
 decide +kernel
def cuts63416 : List PrefixCut := [⟨64,195636525,195636632⟩]
theorem checked63416 : checkPrefixCuts (2^48) 8315994113 10 Manual.Count131072.C063416.packed 64 cuts63416 = true := by
 decide +kernel
def cuts63417 : List PrefixCut := [⟨11,32459114,32459134⟩,
⟨64,193873399,193873514⟩]
theorem checked63417 : checkPrefixCuts (2^48) 8316125185 10 Manual.Count131072.C063417.packed 64 cuts63417 = true := by
 decide +kernel
def pointBounds63417 : List (Nat × Nat × Nat) := [(8316147712,114599931217066,114600320015985)]
theorem point_links_checked63417 : (cuts63417.take 1).map (fun c => (8316125185-1+2*2^10*c.k,114599898757952+c.lower,114600287556851+c.upper)) = pointBounds63417 := by
 decide +kernel
def cuts63418 : List PrefixCut := [⟨64,190993426,190993539⟩]
theorem checked63418 : checkPrefixCuts (2^48) 8316256257 10 Manual.Count131072.C063418.packed 64 cuts63418 = true := by
 decide +kernel
def cuts63419 : List PrefixCut := [⟨10,30901189,30901208⟩,
⟨64,196811859,196811975⟩]
theorem checked63419 : checkPrefixCuts (2^48) 8316387329 10 Manual.Count131072.C063419.packed 64 cuts63419 = true := by
 decide +kernel
def pointBounds63419 : List (Nat × Nat × Nat) := [(8316407808,114600314525966,114600703325112)]
theorem point_links_checked63419 : (cuts63419.take 1).map (fun c => (8316387329-1+2*2^10*c.k,114600283624777+c.lower,114600672423904+c.upper)) = pointBounds63419 := by
 decide +kernel
def cuts63420 : List PrefixCut := [⟨64,196842596,196842710⟩]
theorem checked63420 : checkPrefixCuts (2^48) 8316518401 10 Manual.Count131072.C063420.packed 64 cuts63420 = true := by
 decide +kernel
def cuts63421 : List PrefixCut := [⟨9,27448059,27448075⟩,
⟨64,194368864,194368970⟩]
theorem checked63421 : checkPrefixCuts (2^48) 8316649473 10 Manual.Count131072.C063421.packed 64 cuts63421 = true := by
 decide +kernel
def pointBounds63421 : List (Nat × Nat × Nat) := [(8316667904,114600704727291,114601093526664)]
theorem point_links_checked63421 : (cuts63421.take 1).map (fun c => (8316649473-1+2*2^10*c.k,114600677279232+c.lower,114601066078589+c.upper)) = pointBounds63421 := by
 decide +kernel
def cuts63422 : List PrefixCut := [⟨64,193147411,193147521⟩]
theorem checked63422 : checkPrefixCuts (2^48) 8316780545 10 Manual.Count131072.C063422.packed 64 cuts63422 = true := by
 decide +kernel
def cuts63423 : List PrefixCut := [⟨8,24299739,24299753⟩,
⟨64,194024284,194024397⟩]
theorem checked63423 : checkPrefixCuts (2^48) 8316911617 10 Manual.Count131072.C063423.packed 64 cuts63423 = true := by
 decide +kernel
def pointBounds63423 : List (Nat × Nat × Nat) := [(8316928000,114601089095246,114601477894833)]
theorem point_links_checked63423 : (cuts63423.take 1).map (fun c => (8316911617-1+2*2^10*c.k,114601064795507+c.lower,114601453595080+c.upper)) = pointBounds63423 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000106
