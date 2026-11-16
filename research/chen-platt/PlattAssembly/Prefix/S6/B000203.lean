import PlattAssemblyKernel
import PlattCertificates.Count131072.C056496
import PlattCertificates.Count131072.C056497
import PlattCertificates.Count131072.C056498
import PlattCertificates.Count131072.C056499
import PlattCertificates.Count131072.C056500
import PlattCertificates.Count131072.C056501
import PlattCertificates.Count131072.C056502
import PlattCertificates.Count131072.C056503
import PlattCertificates.Count131072.C056504
import PlattCertificates.Count131072.C056505
import PlattCertificates.Count131072.C056506
import PlattCertificates.Count131072.C056507
import PlattCertificates.Count131072.C056508
import PlattCertificates.Count131072.C056509
import PlattCertificates.Count131072.C056510
import PlattCertificates.Count131072.C056511
import PlattCertificates.Count131072.C056512
import PlattCertificates.Count131072.C056513
import PlattCertificates.Count131072.C056514
import PlattCertificates.Count131072.C056515
import PlattCertificates.Count131072.C056516
import PlattCertificates.Count131072.C056517
import PlattCertificates.Count131072.C056518
import PlattCertificates.Count131072.C056519
import PlattCertificates.Count131072.C056520
import PlattCertificates.Count131072.C056521
import PlattCertificates.Count131072.C056522
import PlattCertificates.Count131072.C056523
import PlattCertificates.Count131072.C056524
import PlattCertificates.Count131072.C056525
import PlattCertificates.Count131072.C056526
import PlattCertificates.Count131072.C056527
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000203
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56496 : List PrefixCut := [⟨64,217155010,217155134⟩]
theorem checked56496 : checkPrefixCuts (2^48) 7408975873 10 Manual.Count131072.C056496.packed 64 cuts56496 = true := by
 decide +kernel
def cuts56497 : List PrefixCut := [⟨34,115832168,115832233⟩,
⟨64,219544543,219544663⟩]
theorem checked56497 : checkPrefixCuts (2^48) 7409106945 10 Manual.Count131072.C056497.packed 64 cuts56497 = true := by
 decide +kernel
def pointBounds56497 : List (Nat × Nat × Nat) := [(7409176576,113173243179870,113173631163424)]
theorem point_links_checked56497 : (cuts56497.take 1).map (fun c => (7409106945-1+2*2^10*c.k,113173127347702+c.lower,113173515331191+c.upper)) = pointBounds56497 := by
 decide +kernel
def cuts56498 : List PrefixCut := [⟨64,218818860,218818984⟩]
theorem checked56498 : checkPrefixCuts (2^48) 7409238017 10 Manual.Count131072.C056498.packed 64 cuts56498 = true := by
 decide +kernel
def cuts56499 : List PrefixCut := [⟨20,69975636,69975674⟩,
⟨64,221094329,221094453⟩]
theorem checked56499 : checkPrefixCuts (2^48) 7409369089 10 Manual.Count131072.C056499.packed 64 cuts56499 = true := by
 decide +kernel
def pointBounds56499 : List (Nat × Nat × Nat) := [(7409410048,113173635686741,113174023670512)]
theorem point_links_checked56499 : (cuts56499.take 1).map (fun c => (7409369089-1+2*2^10*c.k,113173565711105+c.lower,113173953694838+c.upper)) = pointBounds56499 := by
 decide +kernel
def cuts56500 : List PrefixCut := [⟨64,220976449,220976575⟩]
theorem checked56500 : checkPrefixCuts (2^48) 7409500161 10 Manual.Count131072.C056500.packed 64 cuts56500 = true := by
 decide +kernel
def cuts56501 : List PrefixCut := [⟨6,20703283,20703295⟩,
⟨64,220630656,220630780⟩]
theorem checked56501 : checkPrefixCuts (2^48) 7409631233 10 Manual.Count131072.C056501.packed 64 cuts56501 = true := by
 decide +kernel
def pointBounds56501 : List (Nat × Nat × Nat) := [(7409643520,113174028485166,113174416469161)]
theorem point_links_checked56501 : (cuts56501.take 1).map (fun c => (7409631233-1+2*2^10*c.k,113174007781883+c.lower,113174395765866+c.upper)) = pointBounds56501 := by
 decide +kernel
def cuts56502 : List PrefixCut := [⟨56,194340167,194340276⟩,
⟨64,221994269,221994394⟩]
theorem checked56502 : checkPrefixCuts (2^48) 7409762305 10 Manual.Count131072.C056502.packed 64 cuts56502 = true := by
 decide +kernel
def pointBounds56502 : List (Nat × Nat × Nat) := [(7409876992,113174422752706,113174810736922)]
theorem point_links_checked56502 : (cuts56502.take 1).map (fun c => (7409762305-1+2*2^10*c.k,113174228412539+c.lower,113174616396646+c.upper)) = pointBounds56502 := by
 decide +kernel
def cuts56503 : List PrefixCut := [⟨64,221268609,221268735⟩]
theorem checked56503 : checkPrefixCuts (2^48) 7409893377 10 Manual.Count131072.C056503.packed 64 cuts56503 = true := by
 decide +kernel
def cuts56504 : List PrefixCut := [⟨42,144572684,144572764⟩,
⟨64,220808846,220808968⟩]
theorem checked56504 : checkPrefixCuts (2^48) 7410024449 10 Manual.Count131072.C056504.packed 64 cuts56504 = true := by
 decide +kernel
def pointBounds56504 : List (Nat × Nat × Nat) := [(7410110464,113174816248101,113175204232539)]
theorem point_links_checked56504 : (cuts56504.take 1).map (fun c => (7410024449-1+2*2^10*c.k,113174671675417+c.lower,113175059659775+c.upper)) = pointBounds56504 := by
 decide +kernel
def cuts56505 : List PrefixCut := [⟨64,218715815,218715938⟩]
theorem checked56505 : checkPrefixCuts (2^48) 7410155521 10 Manual.Count131072.C056505.packed 64 cuts56505 = true := by
 decide +kernel
def cuts56506 : List PrefixCut := [⟨28,94656623,94656677⟩,
⟨64,218256112,218256236⟩]
theorem checked56506 : checkPrefixCuts (2^48) 7410286593 10 Manual.Count131072.C056506.packed 64 cuts56506 = true := by
 decide +kernel
def pointBounds56506 : List (Nat × Nat × Nat) := [(7410343936,113175205856701,113175593841358)]
theorem point_links_checked56506 : (cuts56506.take 1).map (fun c => (7410286593-1+2*2^10*c.k,113175111200078+c.lower,113175499184681+c.upper)) = pointBounds56506 := by
 decide +kernel
def cuts56507 : List PrefixCut := [⟨64,219011925,219012047⟩]
theorem checked56507 : checkPrefixCuts (2^48) 7410417665 10 Manual.Count131072.C056507.packed 64 cuts56507 = true := by
 decide +kernel
def cuts56508 : List PrefixCut := [⟨14,46415140,46415168⟩,
⟨64,215855499,215855624⟩]
theorem checked56508 : checkPrefixCuts (2^48) 7410548737 10 Manual.Count131072.C056508.packed 64 cuts56508 = true := by
 decide +kernel
def pointBounds56508 : List (Nat × Nat × Nat) := [(7410577408,113175594883255,113175982868132)]
theorem point_links_checked56508 : (cuts56508.take 1).map (fun c => (7410548737-1+2*2^10*c.k,113175548468115+c.lower,113175936452964+c.upper)) = pointBounds56508 := by
 decide +kernel
def cuts56509 : List PrefixCut := [⟨64,220105652,220105777⟩]
theorem checked56509 : checkPrefixCuts (2^48) 7410679809 10 Manual.Count131072.C056509.packed 64 cuts56509 = true := by
 decide +kernel
def pointBounds56509 : List (Nat × Nat × Nat) := [(7410810880,113175984429266,113176372414365)]
theorem point_links_checked56509 : (cuts56509.take 1).map (fun c => (7410679809-1+2*2^10*c.k,113175764323614+c.lower,113176152308588+c.upper)) = pointBounds56509 := by
 decide +kernel
def cuts56510 : List PrefixCut := [⟨64,215657950,215658073⟩]
theorem checked56510 : checkPrefixCuts (2^48) 7410810881 10 Manual.Count131072.C056510.packed 64 cuts56510 = true := by
 decide +kernel
def cuts56511 : List PrefixCut := [⟨50,172736331,172736429⟩,
⟨64,220439701,220439825⟩]
theorem checked56511 : checkPrefixCuts (2^48) 7410941953 10 Manual.Count131072.C056511.packed 64 cuts56511 = true := by
 decide +kernel
def pointBounds56511 : List (Nat × Nat × Nat) := [(7411044352,113176372823547,113176760808867)]
theorem point_links_checked56511 : (cuts56511.take 1).map (fun c => (7410941953-1+2*2^10*c.k,113176200087216+c.lower,113176588072438+c.upper)) = pointBounds56511 := by
 decide +kernel
def cuts56512 : List PrefixCut := [⟨64,218650757,218650880⟩]
theorem checked56512 : checkPrefixCuts (2^48) 7411073025 10 Manual.Count131072.C056512.packed 64 cuts56512 = true := by
 decide +kernel
def cuts56513 : List PrefixCut := [⟨36,122369811,122369881⟩,
⟨64,217089731,217089856⟩]
theorem checked56513 : checkPrefixCuts (2^48) 7411204097 10 Manual.Count131072.C056513.packed 64 cuts56513 = true := by
 decide +kernel
def pointBounds56513 : List (Nat × Nat × Nat) := [(7411277824,113176761547485,113177149533024)]
theorem point_links_checked56513 : (cuts56513.take 1).map (fun c => (7411204097-1+2*2^10*c.k,113176639177674+c.lower,113177027163143+c.upper)) = pointBounds56513 := by
 decide +kernel
def cuts56514 : List PrefixCut := [⟨64,218377154,218377277⟩]
theorem checked56514 : checkPrefixCuts (2^48) 7411335169 10 Manual.Count131072.C056514.packed 64 cuts56514 = true := by
 decide +kernel
def cuts56515 : List PrefixCut := [⟨22,75880417,75880459⟩,
⟨64,217347913,217348033⟩]
theorem checked56515 : checkPrefixCuts (2^48) 7411466241 10 Manual.Count131072.C056515.packed 64 cuts56515 = true := by
 decide +kernel
def pointBounds56515 : List (Nat × Nat × Nat) := [(7411511296,113177150524976,113177538510735)]
theorem point_links_checked56515 : (cuts56515.take 1).map (fun c => (7411466241-1+2*2^10*c.k,113177074644559+c.lower,113177462630276+c.upper)) = pointBounds56515 := by
 decide +kernel
def cuts56516 : List PrefixCut := [⟨64,223268532,223268654⟩]
theorem checked56516 : checkPrefixCuts (2^48) 7411597313 10 Manual.Count131072.C056516.packed 64 cuts56516 = true := by
 decide +kernel
def cuts56517 : List PrefixCut := [⟨8,26887657,26887673⟩,
⟨64,218441527,218441650⟩]
theorem checked56517 : checkPrefixCuts (2^48) 7411728385 10 Manual.Count131072.C056517.packed 64 cuts56517 = true := by
 decide +kernel
def pointBounds56517 : List (Nat × Nat × Nat) := [(7411744768,113177542148661,113177930134636)]
theorem point_links_checked56517 : (cuts56517.take 1).map (fun c => (7411728385-1+2*2^10*c.k,113177515261004+c.lower,113177903246963+c.upper)) = pointBounds56517 := by
 decide +kernel
def cuts56518 : List PrefixCut := [⟨58,197968794,197968903⟩,
⟨64,218133863,218133984⟩]
theorem checked56518 : checkPrefixCuts (2^48) 7411859457 10 Manual.Count131072.C056518.packed 64 cuts56518 = true := by
 decide +kernel
def pointBounds56518 : List (Nat × Nat × Nat) := [(7411978240,113177931671325,113178319657516)]
theorem point_links_checked56518 : (cuts56518.take 1).map (fun c => (7411859457-1+2*2^10*c.k,113177733702531+c.lower,113178121688613+c.upper)) = pointBounds56518 := by
 decide +kernel
def cuts56519 : List PrefixCut := [⟨64,218927492,218927615⟩]
theorem checked56519 : checkPrefixCuts (2^48) 7411990529 10 Manual.Count131072.C056519.packed 64 cuts56519 = true := by
 decide +kernel
def cuts56520 : List PrefixCut := [⟨44,150645697,150645784⟩,
⟨64,219265394,219265521⟩]
theorem checked56520 : checkPrefixCuts (2^48) 7412121601 10 Manual.Count131072.C056520.packed 64 cuts56520 = true := by
 decide +kernel
def pointBounds56520 : List (Nat × Nat × Nat) := [(7412211712,113178321409583,113178709395996)]
theorem point_links_checked56520 : (cuts56520.take 1).map (fun c => (7412121601-1+2*2^10*c.k,113178170763886+c.lower,113178558750212+c.upper)) = pointBounds56520 := by
 decide +kernel
def cuts56521 : List PrefixCut := [⟨64,221539933,221540060⟩]
theorem checked56521 : checkPrefixCuts (2^48) 7412252673 10 Manual.Count131072.C056521.packed 64 cuts56521 = true := by
 decide +kernel
def cuts56522 : List PrefixCut := [⟨30,103895338,103895396⟩,
⟨64,221839810,221839935⟩]
theorem checked56522 : checkPrefixCuts (2^48) 7412383745 10 Manual.Count131072.C056522.packed 64 cuts56522 = true := by
 decide +kernel
def pointBounds56522 : List (Nat × Nat × Nat) := [(7412445184,113178715464551,113179103451189)]
theorem point_links_checked56522 : (cuts56522.take 1).map (fun c => (7412383745-1+2*2^10*c.k,113178611569213+c.lower,113178999555793+c.upper)) = pointBounds56522 := by
 decide +kernel
def cuts56523 : List PrefixCut := [⟨64,216747561,216747683⟩]
theorem checked56523 : checkPrefixCuts (2^48) 7412514817 10 Manual.Count131072.C056523.packed 64 cuts56523 = true := by
 decide +kernel
def cuts56524 : List PrefixCut := [⟨16,55325457,55325489⟩,
⟨64,219401773,219401898⟩]
theorem checked56524 : checkPrefixCuts (2^48) 7412645889 10 Manual.Count131072.C056524.packed 64 cuts56524 = true := by
 decide +kernel
def pointBounds56524 : List (Nat × Nat × Nat) := [(7412678656,113179105482041,113179493468900)]
theorem point_links_checked56524 : (cuts56524.take 1).map (fun c => (7412645889-1+2*2^10*c.k,113179050156584+c.lower,113179438143411+c.upper)) = pointBounds56524 := by
 decide +kernel
def cuts56525 : List PrefixCut := [⟨64,218334698,218334821⟩]
theorem checked56525 : checkPrefixCuts (2^48) 7412776961 10 Manual.Count131072.C056525.packed 64 cuts56525 = true := by
 decide +kernel
def cuts56526 : List PrefixCut := [⟨2,6568967,6568970⟩,
⟨64,218634574,218634694⟩]
theorem checked56526 : checkPrefixCuts (2^48) 7412908033 10 Manual.Count131072.C056526.packed 64 cuts56526 = true := by
 decide +kernel
def pointBounds56526 : List (Nat × Nat × Nat) := [(7412912128,113179494462022,113179882449100)]
theorem point_links_checked56526 : (cuts56526.take 1).map (fun c => (7412908033-1+2*2^10*c.k,113179487893055+c.lower,113179875880130+c.upper)) = pointBounds56526 := by
 decide +kernel
def cuts56527 : List PrefixCut := [⟨52,177737429,177737528⟩,
⟨64,219162302,219162424⟩]
theorem checked56527 : checkPrefixCuts (2^48) 7413039105 10 Manual.Count131072.C056527.packed 64 cuts56527 = true := by
 decide +kernel
def pointBounds56527 : List (Nat × Nat × Nat) := [(7413145600,113179884265058,113180272252352)]
theorem point_links_checked56527 : (cuts56527.take 1).map (fun c => (7413039105-1+2*2^10*c.k,113179706527629+c.lower,113180094514824+c.upper)) = pointBounds56527 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000203
