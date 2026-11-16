import PlattAssemblyKernel
import PlattCertificates.Count131072.C045408
import PlattCertificates.Count131072.C045409
import PlattCertificates.Count131072.C045410
import PlattCertificates.Count131072.C045411
import PlattCertificates.Count131072.C045412
import PlattCertificates.Count131072.C045413
import PlattCertificates.Count131072.C045414
import PlattCertificates.Count131072.C045415
import PlattCertificates.Count131072.C045416
import PlattCertificates.Count131072.C045417
import PlattCertificates.Count131072.C045418
import PlattCertificates.Count131072.C045419
import PlattCertificates.Count131072.C045420
import PlattCertificates.Count131072.C045421
import PlattCertificates.Count131072.C045422
import PlattCertificates.Count131072.C045423
import PlattCertificates.Count131072.C045424
import PlattCertificates.Count131072.C045425
import PlattCertificates.Count131072.C045426
import PlattCertificates.Count131072.C045427
import PlattCertificates.Count131072.C045428
import PlattCertificates.Count131072.C045429
import PlattCertificates.Count131072.C045430
import PlattCertificates.Count131072.C045431
import PlattCertificates.Count131072.C045432
import PlattCertificates.Count131072.C045433
import PlattCertificates.Count131072.C045434
import PlattCertificates.Count131072.C045435
import PlattCertificates.Count131072.C045436
import PlattCertificates.Count131072.C045437
import PlattCertificates.Count131072.C045438
import PlattCertificates.Count131072.C045439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000169
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45408 : List PrefixCut := [⟨64,276195095,276195259⟩]
theorem checked45408 : checkPrefixCuts (2^48) 5955649537 10 Manual.Count131072.C045408.packed 64 cuts45408 = true := by
 decide +kernel
def cuts45409 : List PrefixCut := [⟨25,109408254,109408319⟩,
⟨64,275669163,275669323⟩]
theorem checked45409 : checkPrefixCuts (2^48) 5955780609 10 Manual.Count131072.C045409.packed 64 cuts45409 = true := by
 decide +kernel
def pointBounds45409 : List (Nat × Nat × Nat) := [(5955831808,110455796957541,110456183392106)]
theorem point_links_checked45409 : (cuts45409.take 1).map (fun c => (5955780609-1+2*2^10*c.k,110455687549287+c.lower,110456073983787+c.upper)) = pointBounds45409 := by
 decide +kernel
def cuts45410 : List PrefixCut := [⟨52,223111280,223111413⟩,
⟨64,274859674,274859835⟩]
theorem checked45410 : checkPrefixCuts (2^48) 5955911681 10 Manual.Count131072.C045410.packed 64 cuts45410 = true := by
 decide +kernel
def pointBounds45410 : List (Nat × Nat × Nat) := [(5956018176,110456186329730,110456572764523)]
theorem point_links_checked45410 : (cuts45410.take 1).map (fun c => (5955911681-1+2*2^10*c.k,110455963218450+c.lower,110456349653110+c.upper)) = pointBounds45410 := by
 decide +kernel
def cuts45411 : List PrefixCut := [⟨64,275231678,275231835⟩]
theorem checked45411 : checkPrefixCuts (2^48) 5956042753 10 Manual.Count131072.C045411.packed 64 cuts45411 = true := by
 decide +kernel
def cuts45412 : List PrefixCut := [⟨15,64175750,64175786⟩,
⟨64,279242495,279242656⟩]
theorem checked45412 : checkPrefixCuts (2^48) 5956173825 10 Manual.Count131072.C045412.packed 64 cuts45412 = true := by
 decide +kernel
def pointBounds45412 : List (Nat × Nat × Nat) := [(5956204544,110456577485552,110456963920566)]
theorem point_links_checked45412 : (cuts45412.take 1).map (fun c => (5956173825-1+2*2^10*c.k,110456513309802+c.lower,110456899744780+c.upper)) = pointBounds45412 := by
 decide +kernel
def cuts45413 : List PrefixCut := [⟨42,185906251,185906351⟩,
⟨64,279141880,279142032⟩]
theorem checked45413 : checkPrefixCuts (2^48) 5956304897 10 Manual.Count131072.C045413.packed 64 cuts45413 = true := by
 decide +kernel
def pointBounds45413 : List (Nat × Nat × Nat) := [(5956390912,110456978458548,110457364893787)]
theorem point_links_checked45413 : (cuts45413.take 1).map (fun c => (5956304897-1+2*2^10*c.k,110456792552297+c.lower,110457178987436+c.upper)) = pointBounds45413 := by
 decide +kernel
def cuts45414 : List PrefixCut := [⟨64,274740978,274741140⟩]
theorem checked45414 : checkPrefixCuts (2^48) 5956435969 10 Manual.Count131072.C045414.packed 64 cuts45414 = true := by
 decide +kernel
def cuts45415 : List PrefixCut := [⟨5,21311783,21311795⟩,
⟨64,275774539,275774703⟩]
theorem checked45415 : checkPrefixCuts (2^48) 5956567041 10 Manual.Count131072.C045415.packed 64 cuts45415 = true := by
 decide +kernel
def pointBounds45415 : List (Nat × Nat × Nat) := [(5956577280,110457367746938,110457754182403)]
theorem point_links_checked45415 : (cuts45415.take 1).map (fun c => (5956567041-1+2*2^10*c.k,110457346435155+c.lower,110457732870608+c.upper)) = pointBounds45415 := by
 decide +kernel
def cuts45416 : List PrefixCut := [⟨32,136372886,136372967⟩,
⟨64,272791523,272791681⟩]
theorem checked45416 : checkPrefixCuts (2^48) 5956698113 10 Manual.Count131072.C045416.packed 64 cuts45416 = true := by
 decide +kernel
def pointBounds45416 : List (Nat × Nat × Nat) := [(5956763648,110457758582580,110458145018278)]
theorem point_links_checked45416 : (cuts45416.take 1).map (fun c => (5956698113-1+2*2^10*c.k,110457622209694+c.lower,110458008645311+c.upper)) = pointBounds45416 := by
 decide +kernel
def cuts45417 : List PrefixCut := [⟨59,253837690,253837840⟩,
⟨64,276612899,276613062⟩]
theorem checked45417 : checkPrefixCuts (2^48) 5956829185 10 Manual.Count131072.C045417.packed 64 cuts45417 = true := by
 decide +kernel
def pointBounds45417 : List (Nat × Nat × Nat) := [(5956950016,110458148838907,110458535274832)]
theorem point_links_checked45417 : (cuts45417.take 1).map (fun c => (5956829185-1+2*2^10*c.k,110457895001217+c.lower,110458281436992+c.upper)) = pointBounds45417 := by
 decide +kernel
def cuts45418 : List PrefixCut := [⟨64,272874015,272874174⟩]
theorem checked45418 : checkPrefixCuts (2^48) 5956960257 10 Manual.Count131072.C045418.packed 64 cuts45418 = true := by
 decide +kernel
def cuts45419 : List PrefixCut := [⟨22,93319171,93319225⟩,
⟨64,271214283,271214438⟩]
theorem checked45419 : checkPrefixCuts (2^48) 5957091329 10 Manual.Count131072.C045419.packed 64 cuts45419 = true := by
 decide +kernel
def pointBounds45419 : List (Nat × Nat × Nat) := [(5957136384,110458537807302,110458924243453)]
theorem point_links_checked45419 : (cuts45419.take 1).map (fun c => (5957091329-1+2*2^10*c.k,110458444488131+c.lower,110458830924228+c.upper)) = pointBounds45419 := by
 decide +kernel
def cuts45420 : List PrefixCut := [⟨49,211864345,211864469⟩,
⟨64,277728662,277728823⟩]
theorem checked45420 : checkPrefixCuts (2^48) 5957222401 10 Manual.Count131072.C045420.packed 64 cuts45420 = true := by
 decide +kernel
def pointBounds45420 : List (Nat × Nat × Nat) := [(5957322752,110458927566759,110459314003135)]
theorem point_links_checked45420 : (cuts45420.take 1).map (fun c => (5957222401-1+2*2^10*c.k,110458715702414+c.lower,110459102138666+c.upper)) = pointBounds45420 := by
 decide +kernel
def cuts45421 : List PrefixCut := [⟨64,272714271,272714430⟩]
theorem checked45421 : checkPrefixCuts (2^48) 5957353473 10 Manual.Count131072.C045421.packed 64 cuts45421 = true := by
 decide +kernel
def cuts45422 : List PrefixCut := [⟨12,52066384,52066415⟩,
⟨64,274787112,274787270⟩]
theorem checked45422 : checkPrefixCuts (2^48) 5957484545 10 Manual.Count131072.C045422.packed 64 cuts45422 = true := by
 decide +kernel
def pointBounds45422 : List (Nat × Nat × Nat) := [(5957509120,110459318211731,110459704648334)]
theorem point_links_checked45422 : (cuts45422.take 1).map (fun c => (5957484545-1+2*2^10*c.k,110459266145347+c.lower,110459652581919+c.upper)) = pointBounds45422 := by
 decide +kernel
def cuts45423 : List PrefixCut := [⟨39,167581276,167581372⟩,
⟨64,275537003,275537163⟩]
theorem checked45423 : checkPrefixCuts (2^48) 5957615617 10 Manual.Count131072.C045423.packed 64 cuts45423 = true := by
 decide +kernel
def pointBounds45423 : List (Nat × Nat × Nat) := [(5957695488,110459708513735,110460094950561)]
theorem point_links_checked45423 : (cuts45423.take 1).map (fun c => (5957615617-1+2*2^10*c.k,110459540932459+c.lower,110459927369189+c.upper)) = pointBounds45423 := by
 decide +kernel
def cuts45424 : List PrefixCut := [⟨64,275483707,275483866⟩]
theorem checked45424 : checkPrefixCuts (2^48) 5957746689 10 Manual.Count131072.C045424.packed 64 cuts45424 = true := by
 decide +kernel
def cuts45425 : List PrefixCut := [⟨2,8031503,8031508⟩,
⟨64,279729550,279729710⟩]
theorem checked45425 : checkPrefixCuts (2^48) 5957877761 10 Manual.Count131072.C045425.packed 64 cuts45425 = true := by
 decide +kernel
def pointBounds45425 : List (Nat × Nat × Nat) := [(5957881856,110460099984672,110460486421726)]
theorem point_links_checked45425 : (cuts45425.take 1).map (fun c => (5957877761-1+2*2^10*c.k,110460091953169+c.lower,110460478390218+c.upper)) = pointBounds45425 := by
 decide +kernel
def cuts45426 : List PrefixCut := [⟨29,124437750,124437821⟩,
⟨64,274007068,274007227⟩]
theorem checked45426 : checkPrefixCuts (2^48) 5958008833 10 Manual.Count131072.C045426.packed 64 cuts45426 = true := by
 decide +kernel
def pointBounds45426 : List (Nat × Nat × Nat) := [(5958068224,110460496120469,110460882557749)]
theorem point_links_checked45426 : (cuts45426.take 1).map (fun c => (5958008833-1+2*2^10*c.k,110460371682719+c.lower,110460758119928+c.upper)) = pointBounds45426 := by
 decide +kernel
def cuts45427 : List PrefixCut := [⟨56,239042603,239042741⟩,
⟨64,272394821,272394979⟩]
theorem checked45427 : checkPrefixCuts (2^48) 5958139905 10 Manual.Count131072.C045427.packed 64 cuts45427 = true := by
 decide +kernel
def pointBounds45427 : List (Nat × Nat × Nat) := [(5958254592,110460884732390,110461271169896)]
theorem point_links_checked45427 : (cuts45427.take 1).map (fun c => (5958139905-1+2*2^10*c.k,110460645689787+c.lower,110461032127155+c.upper)) = pointBounds45427 := by
 decide +kernel
def cuts45428 : List PrefixCut := [⟨64,276923928,276924080⟩]
theorem checked45428 : checkPrefixCuts (2^48) 5958270977 10 Manual.Count131072.C045428.packed 64 cuts45428 = true := by
 decide +kernel
def cuts45429 : List PrefixCut := [⟨19,81110809,81110853⟩,
⟨64,274839273,274839440⟩]
theorem checked45429 : checkPrefixCuts (2^48) 5958402049 10 Manual.Count131072.C045429.packed 64 cuts45429 = true := by
 decide +kernel
def pointBounds45429 : List (Nat × Nat × Nat) := [(5958440960,110461276119345,110461662557067)]
theorem point_links_checked45429 : (cuts45429.take 1).map (fun c => (5958402049-1+2*2^10*c.k,110461195008536+c.lower,110461581446214+c.upper)) = pointBounds45429 := by
 decide +kernel
def cuts45430 : List PrefixCut := [⟨46,200433322,200433435⟩,
⟨64,276958985,276959146⟩]
theorem checked45430 : checkPrefixCuts (2^48) 5958533121 10 Manual.Count131072.C045430.packed 64 cuts45430 = true := by
 decide +kernel
def pointBounds45430 : List (Nat × Nat × Nat) := [(5958627328,110461670281131,110462056719089)]
theorem point_links_checked45430 : (cuts45430.take 1).map (fun c => (5958533121-1+2*2^10*c.k,110461469847809+c.lower,110461856285654+c.upper)) = pointBounds45430 := by
 decide +kernel
def cuts45431 : List PrefixCut := [⟨64,277094577,277094734⟩]
theorem checked45431 : checkPrefixCuts (2^48) 5958664193 10 Manual.Count131072.C045431.packed 64 cuts45431 = true := by
 decide +kernel
def cuts45432 : List PrefixCut := [⟨9,37647734,37647758⟩,
⟨64,276332691,276332855⟩]
theorem checked45432 : checkPrefixCuts (2^48) 5958795265 10 Manual.Count131072.C045432.packed 64 cuts45432 = true := by
 decide +kernel
def pointBounds45432 : List (Nat × Nat × Nat) := [(5958813696,110462061549105,110462447987292)]
theorem point_links_checked45432 : (cuts45432.take 1).map (fun c => (5958795265-1+2*2^10*c.k,110462023901371+c.lower,110462410339534+c.upper)) = pointBounds45432 := by
 decide +kernel
def cuts45433 : List PrefixCut := [⟨36,153704482,153704567⟩,
⟨64,275004032,275004182⟩]
theorem checked45433 : checkPrefixCuts (2^48) 5958926337 10 Manual.Count131072.C045433.packed 64 cuts45433 = true := by
 decide +kernel
def pointBounds45433 : List (Nat × Nat × Nat) := [(5959000064,110462453938544,110462840376956)]
theorem point_links_checked45433 : (cuts45433.take 1).map (fun c => (5958926337-1+2*2^10*c.k,110462300234062+c.lower,110462686672389+c.upper)) = pointBounds45433 := by
 decide +kernel
def cuts45434 : List PrefixCut := [⟨63,271077579,271077737⟩,
⟨64,274903514,274903675⟩]
theorem checked45434 : checkPrefixCuts (2^48) 5959057409 10 Manual.Count131072.C045434.packed 64 cuts45434 = true := by
 decide +kernel
def pointBounds45434 : List (Nat × Nat × Nat) := [(5959186432,110462846315673,110463232754308)]
theorem point_links_checked45434 : (cuts45434.take 1).map (fun c => (5959057409-1+2*2^10*c.k,110462575238094+c.lower,110462961676571+c.upper)) = pointBounds45434 := by
 decide +kernel
def cuts45435 : List PrefixCut := [⟨64,277731482,277731644⟩]
theorem checked45435 : checkPrefixCuts (2^48) 5959188481 10 Manual.Count131072.C045435.packed 64 cuts45435 = true := by
 decide +kernel
def cuts45436 : List PrefixCut := [⟨26,113735890,113735953⟩,
⟨64,275836094,275836251⟩]
theorem checked45436 : checkPrefixCuts (2^48) 5959319553 10 Manual.Count131072.C045436.packed 64 cuts45436 = true := by
 decide +kernel
def pointBounds45436 : List (Nat × Nat × Nat) := [(5959372800,110463241608980,110463628047843)]
theorem point_links_checked45436 : (cuts45436.take 1).map (fun c => (5959319553-1+2*2^10*c.k,110463127873090+c.lower,110463514311890+c.upper)) = pointBounds45436 := by
 decide +kernel
def cuts45437 : List PrefixCut := [⟨53,227890811,227890943⟩,
⟨64,276113390,276113551⟩]
theorem checked45437 : checkPrefixCuts (2^48) 5959450625 10 Manual.Count131072.C045437.packed 64 cuts45437 = true := by
 decide +kernel
def pointBounds45437 : List (Nat × Nat × Nat) := [(5959559168,110463631599995,110464018039084)]
theorem point_links_checked45437 : (cuts45437.take 1).map (fun c => (5959450625-1+2*2^10*c.k,110463403709184+c.lower,110463790148141+c.upper)) = pointBounds45437 := by
 decide +kernel
def cuts45438 : List PrefixCut := [⟨64,273320735,273320891⟩]
theorem checked45438 : checkPrefixCuts (2^48) 5959581697 10 Manual.Count131072.C045438.packed 64 cuts45438 = true := by
 decide +kernel
def cuts45439 : List PrefixCut := [⟨16,68955034,68955075⟩,
⟨64,272228476,272228632⟩]
theorem checked45439 : checkPrefixCuts (2^48) 5959712769 10 Manual.Count131072.C045439.packed 64 cuts45439 = true := by
 decide +kernel
def pointBounds45439 : List (Nat × Nat × Nat) := [(5959745536,110464022098343,110464408537658)]
theorem point_links_checked45439 : (cuts45439.take 1).map (fun c => (5959712769-1+2*2^10*c.k,110463953143309+c.lower,110464339582583+c.upper)) = pointBounds45439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000169
