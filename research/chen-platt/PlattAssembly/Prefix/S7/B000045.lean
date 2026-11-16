import PlattAssemblyKernel
import PlattCertificates.Count131072.C061440
import PlattCertificates.Count131072.C061441
import PlattCertificates.Count131072.C061442
import PlattCertificates.Count131072.C061443
import PlattCertificates.Count131072.C061444
import PlattCertificates.Count131072.C061445
import PlattCertificates.Count131072.C061446
import PlattCertificates.Count131072.C061447
import PlattCertificates.Count131072.C061448
import PlattCertificates.Count131072.C061449
import PlattCertificates.Count131072.C061450
import PlattCertificates.Count131072.C061451
import PlattCertificates.Count131072.C061452
import PlattCertificates.Count131072.C061453
import PlattCertificates.Count131072.C061454
import PlattCertificates.Count131072.C061455
import PlattCertificates.Count131072.C061456
import PlattCertificates.Count131072.C061457
import PlattCertificates.Count131072.C061458
import PlattCertificates.Count131072.C061459
import PlattCertificates.Count131072.C061460
import PlattCertificates.Count131072.C061461
import PlattCertificates.Count131072.C061462
import PlattCertificates.Count131072.C061463
import PlattCertificates.Count131072.C061464
import PlattCertificates.Count131072.C061465
import PlattCertificates.Count131072.C061466
import PlattCertificates.Count131072.C061467
import PlattCertificates.Count131072.C061468
import PlattCertificates.Count131072.C061469
import PlattCertificates.Count131072.C061470
import PlattCertificates.Count131072.C061471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61440 : List PrefixCut := [⟨64,200772480,200772597⟩]
theorem checked61440 : checkPrefixCuts (2^48) 8056995841 10 Manual.Count131072.C061440.packed 64 cuts61440 = true := by
 decide +kernel
def cuts61441 : List PrefixCut := [⟨59,184280199,184280302⟩,
⟨64,200594541,200594653⟩]
theorem checked61441 : checkPrefixCuts (2^48) 8057126913 10 Manual.Count131072.C061441.packed 64 cuts61441 = true := by
 decide +kernel
def pointBounds61441 : List (Nat × Nat × Nat) := [(8057247744,114209875693039,114210264267884)]
theorem point_links_checked61441 : (cuts61441.take 1).map (fun c => (8057126913-1+2*2^10*c.k,114209691412840+c.lower,114210079987582+c.upper)) = pointBounds61441 := by
 decide +kernel
def cuts61442 : List PrefixCut := [⟨64,204503886,204504004⟩]
theorem checked61442 : checkPrefixCuts (2^48) 8057257985 10 Manual.Count131072.C061442.packed 64 cuts61442 = true := by
 decide +kernel
def cuts61443 : List PrefixCut := [⟨54,169846768,169846868⟩,
⟨64,202264812,202264929⟩]
theorem checked61443 : checkPrefixCuts (2^48) 8057389057 10 Manual.Count131072.C061443.packed 64 cuts61443 = true := by
 decide +kernel
def pointBounds61443 : List (Nat × Nat × Nat) := [(8057499648,114210266358035,114210654933107)]
theorem point_links_checked61443 : (cuts61443.take 1).map (fun c => (8057389057-1+2*2^10*c.k,114210096511267+c.lower,114210485086239+c.upper)) = pointBounds61443 := by
 decide +kernel
def cuts61444 : List PrefixCut := [⟨64,203169779,203169890⟩]
theorem checked61444 : checkPrefixCuts (2^48) 8057520129 10 Manual.Count131072.C061444.packed 64 cuts61444 = true := by
 decide +kernel
def cuts61445 : List PrefixCut := [⟨49,150209359,150209445⟩,
⟨64,196319761,196319873⟩]
theorem checked61445 : checkPrefixCuts (2^48) 8057651201 10 Manual.Count131072.C061445.packed 64 cuts61445 = true := by
 decide +kernel
def pointBounds61445 : List (Nat × Nat × Nat) := [(8057751552,114210652155217,114211040730503)]
theorem point_links_checked61445 : (cuts61445.take 1).map (fun c => (8057651201-1+2*2^10*c.k,114210501945858+c.lower,114210890521058+c.upper)) = pointBounds61445 := by
 decide +kernel
def cuts61446 : List PrefixCut := [⟨64,199774793,199774907⟩]
theorem checked61446 : checkPrefixCuts (2^48) 8057782273 10 Manual.Count131072.C061446.packed 64 cuts61446 = true := by
 decide +kernel
def cuts61447 : List PrefixCut := [⟨44,139096404,139096478⟩,
⟨64,200574977,200575089⟩]
theorem checked61447 : checkPrefixCuts (2^48) 8057913345 10 Manual.Count131072.C061447.packed 64 cuts61447 = true := by
 decide +kernel
def pointBounds61447 : List (Nat × Nat × Nat) := [(8058003456,114211037136816,114211425712316)]
theorem point_links_checked61447 : (cuts61447.take 1).map (fun c => (8057913345-1+2*2^10*c.k,114210898040412+c.lower,114211286615838+c.upper)) = pointBounds61447 := by
 decide +kernel
def cuts61448 : List PrefixCut := [⟨64,197672474,197672588⟩]
theorem checked61448 : checkPrefixCuts (2^48) 8058044417 10 Manual.Count131072.C061448.packed 64 cuts61448 = true := by
 decide +kernel
def cuts61449 : List PrefixCut := [⟨39,121522086,121522157⟩,
⟨64,200498579,200498694⟩]
theorem checked61449 : checkPrefixCuts (2^48) 8058175489 10 Manual.Count131072.C061449.packed 64 cuts61449 = true := by
 decide +kernel
def pointBounds61449 : List (Nat × Nat × Nat) := [(8058255360,114211417809949,114211806385672)]
theorem point_links_checked61449 : (cuts61449.take 1).map (fun c => (8058175489-1+2*2^10*c.k,114211296287863+c.lower,114211684863515+c.upper)) = pointBounds61449 := by
 decide +kernel
def cuts61450 : List PrefixCut := [⟨64,201368557,201368669⟩]
theorem checked61450 : checkPrefixCuts (2^48) 8058306561 10 Manual.Count131072.C061450.packed 64 cuts61450 = true := by
 decide +kernel
def cuts61451 : List PrefixCut := [⟨34,107476727,107476788⟩,
⟨64,200387280,200387395⟩]
theorem checked61451 : checkPrefixCuts (2^48) 8058437633 10 Manual.Count131072.C061451.packed 64 cuts61451 = true := by
 decide +kernel
def pointBounds61451 : List (Nat × Nat × Nat) := [(8058507264,114211805631726,114212194207666)]
theorem point_links_checked61451 : (cuts61451.take 1).map (fun c => (8058437633-1+2*2^10*c.k,114211698154999+c.lower,114212086730878+c.upper)) = pointBounds61451 := by
 decide +kernel
def cuts61452 : List PrefixCut := [⟨64,201047650,201047767⟩]
theorem checked61452 : checkPrefixCuts (2^48) 8058568705 10 Manual.Count131072.C061452.packed 64 cuts61452 = true := by
 decide +kernel
def cuts61453 : List PrefixCut := [⟨29,93362410,93362464⟩,
⟨64,203384557,203384672⟩]
theorem checked61453 : checkPrefixCuts (2^48) 8058699777 10 Manual.Count131072.C061453.packed 64 cuts61453 = true := by
 decide +kernel
def pointBounds61453 : List (Nat × Nat × Nat) := [(8058759168,114212192952339,114212581528504)]
theorem point_links_checked61453 : (cuts61453.take 1).map (fun c => (8058699777-1+2*2^10*c.k,114212099589929+c.lower,114212488166040+c.upper)) = pointBounds61453 := by
 decide +kernel
def cuts61454 : List PrefixCut := [⟨64,201774591,201774706⟩]
theorem checked61454 : checkPrefixCuts (2^48) 8058830849 10 Manual.Count131072.C061454.packed 64 cuts61454 = true := by
 decide +kernel
def cuts61455 : List PrefixCut := [⟨24,74603724,74603761⟩,
⟨64,200618720,200618827⟩]
theorem checked61455 : checkPrefixCuts (2^48) 8058961921 10 Manual.Count131072.C061455.packed 64 cuts61455 = true := by
 decide +kernel
def pointBounds61455 : List (Nat × Nat × Nat) := [(8059011072,114212579352801,114212967929179)]
theorem point_links_checked61455 : (cuts61455.take 1).map (fun c => (8058961921-1+2*2^10*c.k,114212504749077+c.lower,114212893325418+c.upper)) = pointBounds61455 := by
 decide +kernel
def cuts61456 : List PrefixCut := [⟨64,201209215,201209330⟩]
theorem checked61456 : checkPrefixCuts (2^48) 8059092993 10 Manual.Count131072.C061456.packed 64 cuts61456 = true := by
 decide +kernel
def cuts61457 : List PrefixCut := [⟨19,59967465,59967501⟩,
⟨64,201764740,201764861⟩]
theorem checked61457 : checkPrefixCuts (2^48) 8059224065 10 Manual.Count131072.C061457.packed 64 cuts61457 = true := by
 decide +kernel
def pointBounds61457 : List (Nat × Nat × Nat) := [(8059262976,114212966544477,114213355121076)]
theorem point_links_checked61457 : (cuts61457.take 1).map (fun c => (8059224065-1+2*2^10*c.k,114212906577012+c.lower,114213295153575+c.upper)) = pointBounds61457 := by
 decide +kernel
def cuts61458 : List PrefixCut := [⟨64,203263235,203263351⟩]
theorem checked61458 : checkPrefixCuts (2^48) 8059355137 10 Manual.Count131072.C061458.packed 64 cuts61458 = true := by
 decide +kernel
def cuts61459 : List PrefixCut := [⟨14,44563800,44563824⟩,
⟨64,201967722,201967838⟩]
theorem checked61459 : checkPrefixCuts (2^48) 8059486209 10 Manual.Count131072.C061459.packed 64 cuts61459 = true := by
 decide +kernel
def pointBounds61459 : List (Nat × Nat × Nat) := [(8059514880,114213356168787,114213744745611)]
theorem point_links_checked61459 : (cuts61459.take 1).map (fun c => (8059486209-1+2*2^10*c.k,114213311604987+c.lower,114213700181787+c.upper)) = pointBounds61459 := by
 decide +kernel
def cuts61460 : List PrefixCut := [⟨64,198018058,198018170⟩]
theorem checked61460 : checkPrefixCuts (2^48) 8059617281 10 Manual.Count131072.C061460.packed 64 cuts61460 = true := by
 decide +kernel
def cuts61461 : List PrefixCut := [⟨9,26856165,26856181⟩,
⟨64,199795907,199796021⟩]
theorem checked61461 : checkPrefixCuts (2^48) 8059748353 10 Manual.Count131072.C061461.packed 64 cuts61461 = true := by
 decide +kernel
def pointBounds61461 : List (Nat × Nat × Nat) := [(8059766784,114213738446932,114214127023976)]
theorem point_links_checked61461 : (cuts61461.take 1).map (fun c => (8059748353-1+2*2^10*c.k,114213711590767+c.lower,114214100167795+c.upper)) = pointBounds61461 := by
 decide +kernel
def cuts61462 : List PrefixCut := [⟨64,201888022,201888137⟩]
theorem checked61462 : checkPrefixCuts (2^48) 8059879425 10 Manual.Count131072.C061462.packed 64 cuts61462 = true := by
 decide +kernel
def cuts61463 : List PrefixCut := [⟨4,12956203,12956210⟩,
⟨64,202268882,202269000⟩]
theorem checked61463 : checkPrefixCuts (2^48) 8060010497 10 Manual.Count131072.C061463.packed 64 cuts61463 = true := by
 decide +kernel
def pointBounds61463 : List (Nat × Nat × Nat) := [(8060018688,114214126230899,114214514808163)]
theorem point_links_checked61463 : (cuts61463.take 1).map (fun c => (8060010497-1+2*2^10*c.k,114214113274696+c.lower,114214501851953+c.upper)) = pointBounds61463 := by
 decide +kernel
def cuts61464 : List PrefixCut := [⟨63,196713105,196713217⟩,
⟨64,200065547,200065661⟩]
theorem checked61464 : checkPrefixCuts (2^48) 8060141569 10 Manual.Count131072.C061464.packed 64 cuts61464 = true := by
 decide +kernel
def pointBounds61464 : List (Nat × Nat × Nat) := [(8060270592,114214512256683,114214900834170)]
theorem point_links_checked61464 : (cuts61464.take 1).map (fun c => (8060141569-1+2*2^10*c.k,114214315543578+c.lower,114214704120953+c.upper)) = pointBounds61464 := by
 decide +kernel
def cuts61465 : List PrefixCut := [⟨64,202227387,202227508⟩]
theorem checked61465 : checkPrefixCuts (2^48) 8060272641 10 Manual.Count131072.C061465.packed 64 cuts61465 = true := by
 decide +kernel
def cuts61466 : List PrefixCut := [⟨58,181970398,181970500⟩,
⟨64,200233638,200233751⟩]
theorem checked61466 : checkPrefixCuts (2^48) 8060403713 10 Manual.Count131072.C061466.packed 64 cuts61466 = true := by
 decide +kernel
def pointBounds61466 : List (Nat × Nat × Nat) := [(8060522496,114214899806910,114215288384622)]
theorem point_links_checked61466 : (cuts61466.take 1).map (fun c => (8060403713-1+2*2^10*c.k,114214717836512+c.lower,114215106414122+c.upper)) = pointBounds61466 := by
 decide +kernel
def cuts61467 : List PrefixCut := [⟨64,202220801,202220919⟩]
theorem checked61467 : checkPrefixCuts (2^48) 8060534785 10 Manual.Count131072.C061467.packed 64 cuts61467 = true := by
 decide +kernel
def cuts61468 : List PrefixCut := [⟨53,167054036,167054133⟩,
⟨64,201973076,201973193⟩]
theorem checked61468 : checkPrefixCuts (2^48) 8060665857 10 Manual.Count131072.C061468.packed 64 cuts61468 = true := by
 decide +kernel
def pointBounds61468 : List (Nat × Nat × Nat) := [(8060774400,114215287344987,114215675922925)]
theorem point_links_checked61468 : (cuts61468.take 1).map (fun c => (8060665857-1+2*2^10*c.k,114215120290951+c.lower,114215508868792+c.upper)) = pointBounds61468 := by
 decide +kernel
def cuts61469 : List PrefixCut := [⟨64,200538139,200538259⟩]
theorem checked61469 : checkPrefixCuts (2^48) 8060796929 10 Manual.Count131072.C061469.packed 64 cuts61469 = true := by
 decide +kernel
def cuts61470 : List PrefixCut := [⟨48,150986346,150986428⟩,
⟨64,199731768,199731880⟩]
theorem checked61470 : checkPrefixCuts (2^48) 8060928001 10 Manual.Count131072.C061470.packed 64 cuts61470 = true := by
 decide +kernel
def pointBounds61470 : List (Nat × Nat × Nat) := [(8061026304,114215673788512,114216062366672)]
theorem point_links_checked61470 : (cuts61470.take 1).map (fun c => (8060928001-1+2*2^10*c.k,114215522802166+c.lower,114215911380244+c.upper)) = pointBounds61470 := by
 decide +kernel
def cuts61471 : List PrefixCut := [⟨64,198680994,198681104⟩]
theorem checked61471 : checkPrefixCuts (2^48) 8061059073 10 Manual.Count131072.C061471.packed 64 cuts61471 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000045
