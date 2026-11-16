import PlattAssemblyKernel
import PlattCertificates.Count131072.C056400
import PlattCertificates.Count131072.C056401
import PlattCertificates.Count131072.C056402
import PlattCertificates.Count131072.C056403
import PlattCertificates.Count131072.C056404
import PlattCertificates.Count131072.C056405
import PlattCertificates.Count131072.C056406
import PlattCertificates.Count131072.C056407
import PlattCertificates.Count131072.C056408
import PlattCertificates.Count131072.C056409
import PlattCertificates.Count131072.C056410
import PlattCertificates.Count131072.C056411
import PlattCertificates.Count131072.C056412
import PlattCertificates.Count131072.C056413
import PlattCertificates.Count131072.C056414
import PlattCertificates.Count131072.C056415
import PlattCertificates.Count131072.C056416
import PlattCertificates.Count131072.C056417
import PlattCertificates.Count131072.C056418
import PlattCertificates.Count131072.C056419
import PlattCertificates.Count131072.C056420
import PlattCertificates.Count131072.C056421
import PlattCertificates.Count131072.C056422
import PlattCertificates.Count131072.C056423
import PlattCertificates.Count131072.C056424
import PlattCertificates.Count131072.C056425
import PlattCertificates.Count131072.C056426
import PlattCertificates.Count131072.C056427
import PlattCertificates.Count131072.C056428
import PlattCertificates.Count131072.C056429
import PlattCertificates.Count131072.C056430
import PlattCertificates.Count131072.C056431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56400 : List PrefixCut := [⟨12,41632864,41632888⟩,
⟨64,219579426,219579552⟩]
theorem checked56400 : checkPrefixCuts (2^48) 7396392961 10 Manual.Count131072.C056400.packed 64 cuts56400 = true := by
 decide +kernel
def pointBounds56400 : List (Nat × Nat × Nat) := [(7396417536,113151892897577,113152280869018)]
theorem point_links_checked56400 : (cuts56400.take 1).map (fun c => (7396392961-1+2*2^10*c.k,113151851264713+c.lower,113152239236130+c.upper)) = pointBounds56400 := by
 decide +kernel
def cuts56401 : List PrefixCut := [⟨61,208273384,208273502⟩,
⟨64,219004716,219004840⟩]
theorem checked56401 : checkPrefixCuts (2^48) 7396524033 10 Manual.Count131072.C056401.packed 64 cuts56401 = true := by
 decide +kernel
def pointBounds56401 : List (Nat × Nat × Nat) := [(7396648960,113152279117523,113152667089184)]
theorem point_links_checked56401 : (cuts56401.take 1).map (fun c => (7396524033-1+2*2^10*c.k,113152070844139+c.lower,113152458815682+c.upper)) = pointBounds56401 := by
 decide +kernel
def cuts56402 : List PrefixCut := [⟨64,220522986,220523113⟩]
theorem checked56402 : checkPrefixCuts (2^48) 7396655105 10 Manual.Count131072.C056402.packed 64 cuts56402 = true := by
 decide +kernel
def cuts56403 : List PrefixCut := [⟨46,154382771,154382858⟩,
⟨64,216409317,216409438⟩]
theorem checked56403 : checkPrefixCuts (2^48) 7396786177 10 Manual.Count131072.C056403.packed 64 cuts56403 = true := by
 decide +kernel
def pointBounds56403 : List (Nat × Nat × Nat) := [(7396880384,113152664754612,113153052726493)]
theorem point_links_checked56403 : (cuts56403.take 1).map (fun c => (7396786177-1+2*2^10*c.k,113152510371841+c.lower,113152898343635+c.upper)) = pointBounds56403 := by
 decide +kernel
def cuts56404 : List PrefixCut := [⟨64,218193972,218194100⟩]
theorem checked56404 : checkPrefixCuts (2^48) 7396917249 10 Manual.Count131072.C056404.packed 64 cuts56404 = true := by
 decide +kernel
def cuts56405 : List PrefixCut := [⟨31,107345154,107345215⟩,
⟨64,220206868,220206993⟩]
theorem checked56405 : checkPrefixCuts (2^48) 7397048321 10 Manual.Count131072.C056405.packed 64 cuts56405 = true := by
 decide +kernel
def pointBounds56405 : List (Nat × Nat × Nat) := [(7397111808,113153052320284,113153440292388)]
theorem point_links_checked56405 : (cuts56405.take 1).map (fun c => (7397048321-1+2*2^10*c.k,113152944975130+c.lower,113153332947173+c.upper)) = pointBounds56405 := by
 decide +kernel
def cuts56406 : List PrefixCut := [⟨64,217501292,217501417⟩]
theorem checked56406 : checkPrefixCuts (2^48) 7397179393 10 Manual.Count131072.C056406.packed 64 cuts56406 = true := by
 decide +kernel
def cuts56407 : List PrefixCut := [⟨16,54793288,54793320⟩,
⟨64,216698408,216698534⟩]
theorem checked56407 : checkPrefixCuts (2^48) 7397310465 10 Manual.Count131072.C056407.packed 64 cuts56407 = true := by
 decide +kernel
def pointBounds56407 : List (Nat × Nat × Nat) := [(7397343232,113153437476578,113153825448903)]
theorem point_links_checked56407 : (cuts56407.take 1).map (fun c => (7397310465-1+2*2^10*c.k,113153382683290+c.lower,113153770655583+c.upper)) = pointBounds56407 := by
 decide +kernel
def cuts56408 : List PrefixCut := [⟨64,219548289,219548415⟩]
theorem checked56408 : checkPrefixCuts (2^48) 7397441537 10 Manual.Count131072.C056408.packed 64 cuts56408 = true := by
 decide +kernel
def cuts56409 : List PrefixCut := [⟨1,3766913,3766915⟩,
⟨64,218402939,218403063⟩]
theorem checked56409 : checkPrefixCuts (2^48) 7397572609 10 Manual.Count131072.C056409.packed 64 cuts56409 = true := by
 decide +kernel
def pointBounds56409 : List (Nat × Nat × Nat) := [(7397574656,113153822696900,113154210669447)]
theorem point_links_checked56409 : (cuts56409.take 1).map (fun c => (7397572609-1+2*2^10*c.k,113153818929987+c.lower,113154206902532+c.upper)) = pointBounds56409 := by
 decide +kernel
def cuts56410 : List PrefixCut := [⟨50,171942024,171942123⟩,
⟨64,218132728,218132852⟩]
theorem checked56410 : checkPrefixCuts (2^48) 7397703681 10 Manual.Count131072.C056410.packed 64 cuts56410 = true := by
 decide +kernel
def pointBounds56410 : List (Nat × Nat × Nat) := [(7397806080,113154209274950,113154597247718)]
theorem point_links_checked56410 : (cuts56410.take 1).map (fun c => (7397703681-1+2*2^10*c.k,113154037332926+c.lower,113154425305595+c.upper)) = pointBounds56410 := by
 decide +kernel
def cuts56411 : List PrefixCut := [⟨64,219498584,219498710⟩]
theorem checked56411 : checkPrefixCuts (2^48) 7397834753 10 Manual.Count131072.C056411.packed 64 cuts56411 = true := by
 decide +kernel
def cuts56412 : List PrefixCut := [⟨35,125176017,125176085⟩,
⟨64,225011566,225011692⟩]
theorem checked56412 : checkPrefixCuts (2^48) 7397965825 10 Manual.Count131072.C056412.packed 64 cuts56412 = true := by
 decide +kernel
def pointBounds56412 : List (Nat × Nat × Nat) := [(7398037504,113154600140255,113154988113242)]
theorem point_links_checked56412 : (cuts56412.take 1).map (fun c => (7397965825-1+2*2^10*c.k,113154474964238+c.lower,113154862937157+c.upper)) = pointBounds56412 := by
 decide +kernel
def cuts56413 : List PrefixCut := [⟨64,220670269,220670396⟩]
theorem checked56413 : checkPrefixCuts (2^48) 7398096897 10 Manual.Count131072.C056413.packed 64 cuts56413 = true := by
 decide +kernel
def cuts56414 : List PrefixCut := [⟨20,66770997,66771035⟩,
⟨64,215644287,215644410⟩]
theorem checked56414 : checkPrefixCuts (2^48) 7398227969 10 Manual.Count131072.C056414.packed 64 cuts56414 = true := by
 decide +kernel
def pointBounds56414 : List (Nat × Nat × Nat) := [(7398268928,113154987417070,113155375390280)]
theorem point_links_checked56414 : (cuts56414.take 1).map (fun c => (7398227969-1+2*2^10*c.k,113154920646073+c.lower,113155308619245+c.upper)) = pointBounds56414 := by
 decide +kernel
def cuts56415 : List PrefixCut := [⟨64,219711315,219711441⟩]
theorem checked56415 : checkPrefixCuts (2^48) 7398359041 10 Manual.Count131072.C056415.packed 64 cuts56415 = true := by
 decide +kernel
def cuts56416 : List PrefixCut := [⟨5,17006064,17006074⟩,
⟨64,221343328,221343454⟩]
theorem checked56416 : checkPrefixCuts (2^48) 7398490113 10 Manual.Count131072.C056416.packed 64 cuts56416 = true := by
 decide +kernel
def pointBounds56416 : List (Nat × Nat × Nat) := [(7398500352,113155373007739,113155760981170)]
theorem point_links_checked56416 : (cuts56416.take 1).map (fun c => (7398490113-1+2*2^10*c.k,113155356001675+c.lower,113155743975096+c.upper)) = pointBounds56416 := by
 decide +kernel
def cuts56417 : List PrefixCut := [⟨54,184627309,184627413⟩,
⟨64,219018737,219018861⟩]
theorem checked56417 : checkPrefixCuts (2^48) 7398621185 10 Manual.Count131072.C056417.packed 64 cuts56417 = true := by
 decide +kernel
def pointBounds56417 : List (Nat × Nat × Nat) := [(7398731776,113155761972312,113156149945963)]
theorem point_links_checked56417 : (cuts56417.take 1).map (fun c => (7398621185-1+2*2^10*c.k,113155577345003+c.lower,113155965318550+c.upper)) = pointBounds56417 := by
 decide +kernel
def cuts56418 : List PrefixCut := [⟨64,220802866,220802993⟩]
theorem checked56418 : checkPrefixCuts (2^48) 7398752257 10 Manual.Count131072.C056418.packed 64 cuts56418 = true := by
 decide +kernel
def cuts56419 : List PrefixCut := [⟨39,134366749,134366823⟩,
⟨64,219581602,219581723⟩]
theorem checked56419 : checkPrefixCuts (2^48) 7398883329 10 Manual.Count131072.C056419.packed 64 cuts56419 = true := by
 decide +kernel
def pointBounds56419 : List (Nat × Nat × Nat) := [(7398963200,113156151533355,113156539507227)]
theorem point_links_checked56419 : (cuts56419.take 1).map (fun c => (7398883329-1+2*2^10*c.k,113156017166606+c.lower,113156405140404+c.upper)) = pointBounds56419 := by
 decide +kernel
def cuts56420 : List PrefixCut := [⟨64,222354766,222354893⟩]
theorem checked56420 : checkPrefixCuts (2^48) 7399014401 10 Manual.Count131072.C056420.packed 64 cuts56420 = true := by
 decide +kernel
def cuts56421 : List PrefixCut := [⟨24,83044403,83044451⟩,
⟨64,219649922,219650045⟩]
theorem checked56421 : checkPrefixCuts (2^48) 7399145473 10 Manual.Count131072.C056421.packed 64 cuts56421 = true := by
 decide +kernel
def pointBounds56421 : List (Nat × Nat × Nat) := [(7399194624,113156542147377,113156930121471)]
theorem point_links_checked56421 : (cuts56421.take 1).map (fun c => (7399145473-1+2*2^10*c.k,113156459102974+c.lower,113156847077020+c.upper)) = pointBounds56421 := by
 decide +kernel
def cuts56422 : List PrefixCut := [⟨64,217820057,217820180⟩]
theorem checked56422 : checkPrefixCuts (2^48) 7399276545 10 Manual.Count131072.C056422.packed 64 cuts56422 = true := by
 decide +kernel
def cuts56423 : List PrefixCut := [⟨9,31002718,31002735⟩,
⟨64,216827185,216827308⟩]
theorem checked56423 : checkPrefixCuts (2^48) 7399407617 10 Manual.Count131072.C056423.packed 64 cuts56423 = true := by
 decide +kernel
def pointBounds56423 : List (Nat × Nat × Nat) := [(7399426048,113156927575671,113157315549980)]
theorem point_links_checked56423 : (cuts56423.take 1).map (fun c => (7399407617-1+2*2^10*c.k,113156896572953+c.lower,113157284547245+c.upper)) = pointBounds56423 := by
 decide +kernel
def cuts56424 : List PrefixCut := [⟨58,198108235,198108350⟩,
⟨64,217926489,217926616⟩]
theorem checked56424 : checkPrefixCuts (2^48) 7399538689 10 Manual.Count131072.C056424.packed 64 cuts56424 = true := by
 decide +kernel
def pointBounds56424 : List (Nat × Nat × Nat) := [(7399657472,113157311508373,113157699482903)]
theorem point_links_checked56424 : (cuts56424.take 1).map (fun c => (7399538689-1+2*2^10*c.k,113157113400138+c.lower,113157501374553+c.upper)) = pointBounds56424 := by
 decide +kernel
def cuts56425 : List PrefixCut := [⟨64,219063764,219063885⟩]
theorem checked56425 : checkPrefixCuts (2^48) 7399669761 10 Manual.Count131072.C056425.packed 64 cuts56425 = true := by
 decide +kernel
def cuts56426 : List PrefixCut := [⟨43,144277935,144278021⟩,
⟨64,216701542,216701670⟩]
theorem checked56426 : checkPrefixCuts (2^48) 7399800833 10 Manual.Count131072.C056426.packed 64 cuts56426 = true := by
 decide +kernel
def pointBounds56426 : List (Nat × Nat × Nat) := [(7399888896,113157694668326,113158082643075)]
theorem point_links_checked56426 : (cuts56426.take 1).map (fun c => (7399800833-1+2*2^10*c.k,113157550390391+c.lower,113157938365054+c.upper)) = pointBounds56426 := by
 decide +kernel
def cuts56427 : List PrefixCut := [⟨64,223278155,223278279⟩]
theorem checked56427 : checkPrefixCuts (2^48) 7399931905 10 Manual.Count131072.C056427.packed 64 cuts56427 = true := by
 decide +kernel
def cuts56428 : List PrefixCut := [⟨28,94521142,94521198⟩,
⟨64,217758890,217759016⟩]
theorem checked56428 : checkPrefixCuts (2^48) 7400062977 10 Manual.Count131072.C056428.packed 64 cuts56428 = true := by
 decide +kernel
def pointBounds56428 : List (Nat × Nat × Nat) := [(7400120320,113158084891230,113158472866201)]
theorem point_links_checked56428 : (cuts56428.take 1).map (fun c => (7400062977-1+2*2^10*c.k,113157990370088+c.lower,113158378345003+c.upper)) = pointBounds56428 := by
 decide +kernel
def cuts56429 : List PrefixCut := [⟨64,220151299,220151423⟩]
theorem checked56429 : checkPrefixCuts (2^48) 7400194049 10 Manual.Count131072.C056429.packed 64 cuts56429 = true := by
 decide +kernel
def cuts56430 : List PrefixCut := [⟨13,44767675,44767699⟩,
⟨64,220375595,220375719⟩]
theorem checked56430 : checkPrefixCuts (2^48) 7400325121 10 Manual.Count131072.C056430.packed 64 cuts56430 = true := by
 decide +kernel
def pointBounds56430 : List (Nat × Nat × Nat) := [(7400351744,113158473047952,113158861023141)]
theorem point_links_checked56430 : (cuts56430.take 1).map (fun c => (7400325121-1+2*2^10*c.k,113158428280277+c.lower,113158816255442+c.upper)) = pointBounds56430 := by
 decide +kernel
def cuts56431 : List PrefixCut := [⟨62,213715737,213715861⟩,
⟨64,221474702,221474830⟩]
theorem checked56431 : checkPrefixCuts (2^48) 7400456193 10 Manual.Count131072.C056431.packed 64 cuts56431 = true := by
 decide +kernel
def pointBounds56431 : List (Nat × Nat × Nat) := [(7400583168,113158862371609,113159250347022)]
theorem point_links_checked56431 : (cuts56431.take 1).map (fun c => (7400456193-1+2*2^10*c.k,113158648655872+c.lower,113159036631161+c.upper)) = pointBounds56431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000200
