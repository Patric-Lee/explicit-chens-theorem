import PlattAssemblyKernel
import PlattCertificates.Count131072.C069536
import PlattCertificates.Count131072.C069537
import PlattCertificates.Count131072.C069538
import PlattCertificates.Count131072.C069539
import PlattCertificates.Count131072.C069540
import PlattCertificates.Count131072.C069541
import PlattCertificates.Count131072.C069542
import PlattCertificates.Count131072.C069543
import PlattCertificates.Count131072.C069544
import PlattCertificates.Count131072.C069545
import PlattCertificates.Count131072.C069546
import PlattCertificates.Count131072.C069547
import PlattCertificates.Count131072.C069548
import PlattCertificates.Count131072.C069549
import PlattCertificates.Count131072.C069550
import PlattCertificates.Count131072.C069551
import PlattCertificates.Count131072.C069552
import PlattCertificates.Count131072.C069553
import PlattCertificates.Count131072.C069554
import PlattCertificates.Count131072.C069555
import PlattCertificates.Count131072.C069556
import PlattCertificates.Count131072.C069557
import PlattCertificates.Count131072.C069558
import PlattCertificates.Count131072.C069559
import PlattCertificates.Count131072.C069560
import PlattCertificates.Count131072.C069561
import PlattCertificates.Count131072.C069562
import PlattCertificates.Count131072.C069563
import PlattCertificates.Count131072.C069564
import PlattCertificates.Count131072.C069565
import PlattCertificates.Count131072.C069566
import PlattCertificates.Count131072.C069567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000298
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69536 : List PrefixCut := [⟨64,175215286,175215390⟩]
theorem checked69536 : checkPrefixCuts (2^48) 9118154753 10 Manual.Count131072.C069536.packed 64 cuts69536 = true := by
 decide +kernel
def cuts69537 : List PrefixCut := [⟨50,137954031,137954115⟩,
⟨64,176848824,176848926⟩]
theorem checked69537 : checkPrefixCuts (2^48) 9118285825 10 Manual.Count131072.C069537.packed 64 cuts69537 = true := by
 decide +kernel
def pointBounds69537 : List (Nat × Nat × Nat) := [(9118388224,115732503445353,115732892902823)]
theorem point_links_checked69537 : (cuts69537.take 1).map (fun c => (9118285825-1+2*2^10*c.k,115732365491322+c.lower,115732754948708+c.upper)) = pointBounds69537 := by
 decide +kernel
def cuts69538 : List PrefixCut := [⟨64,171475131,171475237⟩]
theorem checked69538 : checkPrefixCuts (2^48) 9118416897 10 Manual.Count131072.C069538.packed 64 cuts69538 = true := by
 decide +kernel
def cuts69539 : List PrefixCut := [⟨62,170237991,170238091⟩,
⟨64,175701619,175701722⟩]
theorem checked69539 : checkPrefixCuts (2^48) 9118547969 10 Manual.Count131072.C069539.packed 64 cuts69539 = true := by
 decide +kernel
def pointBounds69539 : List (Nat × Nat × Nat) := [(9118674944,115732884053268,115733273510962)]
theorem point_links_checked69539 : (cuts69539.take 1).map (fun c => (9118547969-1+2*2^10*c.k,115732713815277+c.lower,115733103272871+c.upper)) = pointBounds69539 := by
 decide +kernel
def cuts69540 : List PrefixCut := [⟨64,180884872,180884978⟩]
theorem checked69540 : checkPrefixCuts (2^48) 9118679041 10 Manual.Count131072.C069540.packed 64 cuts69540 = true := by
 decide +kernel
def cuts69541 : List PrefixCut := [⟨64,175912630,175912731⟩]
theorem checked69541 : checkPrefixCuts (2^48) 9118810113 10 Manual.Count131072.C069541.packed 64 cuts69541 = true := by
 decide +kernel
def cuts69542 : List PrefixCut := [⟨10,27440783,27440801⟩,
⟨64,178996780,178996885⟩]
theorem checked69542 : checkPrefixCuts (2^48) 9118941185 10 Manual.Count131072.C069542.packed 64 cuts69542 = true := by
 decide +kernel
def pointBounds69542 : List (Nat × Nat × Nat) := [(9118961664,115733273755181,115733663213103)]
theorem point_links_checked69542 : (cuts69542.take 1).map (fun c => (9118941185-1+2*2^10*c.k,115733246314398+c.lower,115733635772302+c.upper)) = pointBounds69542 := by
 decide +kernel
def cuts69543 : List PrefixCut := [⟨64,177358297,177358400⟩]
theorem checked69543 : checkPrefixCuts (2^48) 9119072257 10 Manual.Count131072.C069543.packed 64 cuts69543 = true := by
 decide +kernel
def cuts69544 : List PrefixCut := [⟨22,61701323,61701357⟩,
⟨64,175225997,175226100⟩]
theorem checked69544 : checkPrefixCuts (2^48) 9119203329 10 Manual.Count131072.C069544.packed 64 cuts69544 = true := by
 decide +kernel
def pointBounds69544 : List (Nat × Nat × Nat) := [(9119248384,115733664370798,115734053828944)]
theorem point_links_checked69544 : (cuts69544.take 1).map (fun c => (9119203329-1+2*2^10*c.k,115733602669475+c.lower,115733992127587+c.upper)) = pointBounds69544 := by
 decide +kernel
def cuts69545 : List PrefixCut := [⟨64,176149445,176149546⟩]
theorem checked69545 : checkPrefixCuts (2^48) 9119334401 10 Manual.Count131072.C069545.packed 64 cuts69545 = true := by
 decide +kernel
def cuts69546 : List PrefixCut := [⟨34,93675777,93675834⟩,
⟨64,176146914,176147020⟩]
theorem checked69546 : checkPrefixCuts (2^48) 9119465473 10 Manual.Count131072.C069546.packed 64 cuts69546 = true := by
 decide +kernel
def pointBounds69546 : List (Nat × Nat × Nat) := [(9119535104,115734047720694,115734437179067)]
theorem point_links_checked69546 : (cuts69546.take 1).map (fun c => (9119465473-1+2*2^10*c.k,115733954044917+c.lower,115734343503233+c.upper)) = pointBounds69546 := by
 decide +kernel
def cuts69547 : List PrefixCut := [⟨64,174848071,174848170⟩]
theorem checked69547 : checkPrefixCuts (2^48) 9119596545 10 Manual.Count131072.C069547.packed 64 cuts69547 = true := by
 decide +kernel
def cuts69548 : List PrefixCut := [⟨46,125895229,125895301⟩,
⟨64,175431975,175432077⟩]
theorem checked69548 : checkPrefixCuts (2^48) 9119727617 10 Manual.Count131072.C069548.packed 64 cuts69548 = true := by
 decide +kernel
def pointBounds69548 : List (Nat × Nat × Nat) := [(9119821824,115734430935131,115734820393724)]
theorem point_links_checked69548 : (cuts69548.take 1).map (fun c => (9119727617-1+2*2^10*c.k,115734305039902+c.lower,115734694498423+c.upper)) = pointBounds69548 := by
 decide +kernel
def cuts69549 : List PrefixCut := [⟨64,174657861,174657966⟩]
theorem checked69549 : checkPrefixCuts (2^48) 9119858689 10 Manual.Count131072.C069549.packed 64 cuts69549 = true := by
 decide +kernel
def cuts69550 : List PrefixCut := [⟨58,160520059,160520155⟩,
⟨64,177402169,177402273⟩]
theorem checked69550 : checkPrefixCuts (2^48) 9119989761 10 Manual.Count131072.C069550.packed 64 cuts69550 = true := by
 decide +kernel
def pointBounds69550 : List (Nat × Nat × Nat) := [(9120108544,115734815649797,115735205108621)]
theorem point_links_checked69550 : (cuts69550.take 1).map (fun c => (9119989761-1+2*2^10*c.k,115734655129738+c.lower,115735044588466+c.upper)) = pointBounds69550 := by
 decide +kernel
def cuts69551 : List PrefixCut := [⟨64,176874964,176875064⟩]
theorem checked69551 : checkPrefixCuts (2^48) 9120120833 10 Manual.Count131072.C069551.packed 64 cuts69551 = true := by
 decide +kernel
def cuts69552 : List PrefixCut := [⟨64,178076056,178076159⟩]
theorem checked69552 : checkPrefixCuts (2^48) 9120251905 10 Manual.Count131072.C069552.packed 64 cuts69552 = true := by
 decide +kernel
def cuts69553 : List PrefixCut := [⟨6,17282810,17282819⟩,
⟨64,180789343,180789450⟩]
theorem checked69553 : checkPrefixCuts (2^48) 9120382977 10 Manual.Count131072.C069553.packed 64 cuts69553 = true := by
 decide +kernel
def pointBounds69553 : List (Nat × Nat × Nat) := [(9120395264,115735204765737,115735594224781)]
theorem point_links_checked69553 : (cuts69553.take 1).map (fun c => (9120382977-1+2*2^10*c.k,115735187482927+c.lower,115735576941962+c.upper)) = pointBounds69553 := by
 decide +kernel
def cuts69554 : List PrefixCut := [⟨64,175169944,175170050⟩]
theorem checked69554 : checkPrefixCuts (2^48) 9120514049 10 Manual.Count131072.C069554.packed 64 cuts69554 = true := by
 decide +kernel
def cuts69555 : List PrefixCut := [⟨18,48390408,48390439⟩,
⟨64,175136572,175136676⟩]
theorem checked69555 : checkPrefixCuts (2^48) 9120645121 10 Manual.Count131072.C069555.packed 64 cuts69555 = true := by
 decide +kernel
def pointBounds69555 : List (Nat × Nat × Nat) := [(9120681984,115735591832622,115735981291901)]
theorem point_links_checked69555 : (cuts69555.take 1).map (fun c => (9120645121-1+2*2^10*c.k,115735543442214+c.lower,115735932901462+c.upper)) = pointBounds69555 := by
 decide +kernel
def cuts69556 : List PrefixCut := [⟨64,175134059,175134161⟩]
theorem checked69556 : checkPrefixCuts (2^48) 9120776193 10 Manual.Count131072.C069556.packed 64 cuts69556 = true := by
 decide +kernel
def cuts69557 : List PrefixCut := [⟨30,82304427,82304470⟩,
⟨64,179637117,179637217⟩]
theorem checked69557 : checkPrefixCuts (2^48) 9120907265 10 Manual.Count131072.C069557.packed 64 cuts69557 = true := by
 decide +kernel
def pointBounds69557 : List (Nat × Nat × Nat) := [(9120968704,115735976017272,115736365476769)]
theorem point_links_checked69557 : (cuts69557.take 1).map (fun c => (9120907265-1+2*2^10*c.k,115735893712845+c.lower,115736283172299+c.upper)) = pointBounds69557 := by
 decide +kernel
def cuts69558 : List PrefixCut := [⟨64,175931389,175931487⟩]
theorem checked69558 : checkPrefixCuts (2^48) 9121038337 10 Manual.Count131072.C069558.packed 64 cuts69558 = true := by
 decide +kernel
def cuts69559 : List PrefixCut := [⟨42,114025383,114025455⟩,
⟨64,174848772,174848879⟩]
theorem checked69559 : checkPrefixCuts (2^48) 9121169409 10 Manual.Count131072.C069559.packed 64 cuts69559 = true := by
 decide +kernel
def pointBounds69559 : List (Nat × Nat × Nat) := [(9121255424,115736363306734,115736752766458)]
theorem point_links_checked69559 : (cuts69559.take 1).map (fun c => (9121169409-1+2*2^10*c.k,115736249281351+c.lower,115736638741003+c.upper)) = pointBounds69559 := by
 decide +kernel
def cuts69560 : List PrefixCut := [⟨64,174506807,174506911⟩]
theorem checked69560 : checkPrefixCuts (2^48) 9121300481 10 Manual.Count131072.C069560.packed 64 cuts69560 = true := by
 decide +kernel
def cuts69561 : List PrefixCut := [⟨54,149015434,149015520⟩,
⟨64,176448393,176448496⟩]
theorem checked69561 : checkPrefixCuts (2^48) 9121431553 10 Manual.Count131072.C069561.packed 64 cuts69561 = true := by
 decide +kernel
def pointBounds69561 : List (Nat × Nat × Nat) := [(9121542144,115736747652364,115737137112313)]
theorem point_links_checked69561 : (cuts69561.take 1).map (fun c => (9121431553-1+2*2^10*c.k,115736598636930+c.lower,115736988096793+c.upper)) = pointBounds69561 := by
 decide +kernel
def cuts69562 : List PrefixCut := [⟨64,174131513,174131614⟩]
theorem checked69562 : checkPrefixCuts (2^48) 9121562625 10 Manual.Count131072.C069562.packed 64 cuts69562 = true := by
 decide +kernel
def cuts69563 : List PrefixCut := [⟨64,175887886,175887989⟩]
theorem checked69563 : checkPrefixCuts (2^48) 9121693697 10 Manual.Count131072.C069563.packed 64 cuts69563 = true := by
 decide +kernel
def cuts69564 : List PrefixCut := [⟨2,5708600,5708603⟩,
⟨64,176379072,176379182⟩]
theorem checked69564 : checkPrefixCuts (2^48) 9121824769 10 Manual.Count131072.C069564.packed 64 cuts69564 = true := by
 decide +kernel
def pointBounds69564 : List (Nat × Nat × Nat) := [(9121828864,115737130813322,115737520273495)]
theorem point_links_checked69564 : (cuts69564.take 1).map (fun c => (9121824769-1+2*2^10*c.k,115737125104722+c.lower,115737514564892+c.upper)) = pointBounds69564 := by
 decide +kernel
def cuts69565 : List PrefixCut := [⟨64,176067965,176068074⟩]
theorem checked69565 : checkPrefixCuts (2^48) 9121955841 10 Manual.Count131072.C069565.packed 64 cuts69565 = true := by
 decide +kernel
def cuts69566 : List PrefixCut := [⟨14,36996787,36996806⟩,
⟨64,177330522,177330628⟩]
theorem checked69566 : checkPrefixCuts (2^48) 9122086913 10 Manual.Count131072.C069566.packed 64 cuts69566 = true := by
 decide +kernel
def pointBounds69566 : List (Nat × Nat × Nat) := [(9122115584,115737514548546,115737904008954)]
theorem point_links_checked69566 : (cuts69566.take 1).map (fun c => (9122086913-1+2*2^10*c.k,115737477551759+c.lower,115737867012148+c.upper)) = pointBounds69566 := by
 decide +kernel
def cuts69567 : List PrefixCut := [⟨64,172946476,172946585⟩]
theorem checked69567 : checkPrefixCuts (2^48) 9122217985 10 Manual.Count131072.C069567.packed 64 cuts69567 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000298
