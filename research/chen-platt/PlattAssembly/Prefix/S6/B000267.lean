import PlattAssemblyKernel
import PlattCertificates.Count131072.C058544
import PlattCertificates.Count131072.C058545
import PlattCertificates.Count131072.C058546
import PlattCertificates.Count131072.C058547
import PlattCertificates.Count131072.C058548
import PlattCertificates.Count131072.C058549
import PlattCertificates.Count131072.C058550
import PlattCertificates.Count131072.C058551
import PlattCertificates.Count131072.C058552
import PlattCertificates.Count131072.C058553
import PlattCertificates.Count131072.C058554
import PlattCertificates.Count131072.C058555
import PlattCertificates.Count131072.C058556
import PlattCertificates.Count131072.C058557
import PlattCertificates.Count131072.C058558
import PlattCertificates.Count131072.C058559
import PlattCertificates.Count131072.C058560
import PlattCertificates.Count131072.C058561
import PlattCertificates.Count131072.C058562
import PlattCertificates.Count131072.C058563
import PlattCertificates.Count131072.C058564
import PlattCertificates.Count131072.C058565
import PlattCertificates.Count131072.C058566
import PlattCertificates.Count131072.C058567
import PlattCertificates.Count131072.C058568
import PlattCertificates.Count131072.C058569
import PlattCertificates.Count131072.C058570
import PlattCertificates.Count131072.C058571
import PlattCertificates.Count131072.C058572
import PlattCertificates.Count131072.C058573
import PlattCertificates.Count131072.C058574
import PlattCertificates.Count131072.C058575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000267
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58544 : List PrefixCut := [⟨64,211065567,211065690⟩]
theorem checked58544 : checkPrefixCuts (2^48) 7677411329 10 Manual.Count131072.C058544.packed 64 cuts58544 = true := by
 decide +kernel
def cuts58545 : List PrefixCut := [⟨50,165455001,165455092⟩,
⟨64,210732018,210732135⟩]
theorem checked58545 : checkPrefixCuts (2^48) 7677542401 10 Manual.Count131072.C058545.packed 64 cuts58545 = true := by
 decide +kernel
def pointBounds58545 : List (Nat × Nat × Nat) := [(7677644800,113613693075570,113614081309814)]
theorem point_links_checked58545 : (cuts58545.take 1).map (fun c => (7677542401-1+2*2^10*c.k,113613527620569+c.lower,113613915854722+c.upper)) = pointBounds58545 := by
 decide +kernel
def cuts58546 : List PrefixCut := [⟨64,215054426,215054545⟩]
theorem checked58546 : checkPrefixCuts (2^48) 7677673473 10 Manual.Count131072.C058546.packed 64 cuts58546 = true := by
 decide +kernel
def cuts58547 : List PrefixCut := [⟨40,129962047,129962124⟩,
⟨64,209405023,209405147⟩]
theorem checked58547 : checkPrefixCuts (2^48) 7677804545 10 Manual.Count131072.C058547.packed 64 cuts58547 = true := by
 decide +kernel
def pointBounds58547 : List (Nat × Nat × Nat) := [(7677886464,113614083369060,113614471603526)]
theorem point_links_checked58547 : (cuts58547.take 1).map (fun c => (7677804545-1+2*2^10*c.k,113613953407013+c.lower,113614341641402+c.upper)) = pointBounds58547 := by
 decide +kernel
def cuts58548 : List PrefixCut := [⟨64,212004307,212004430⟩]
theorem checked58548 : checkPrefixCuts (2^48) 7677935617 10 Manual.Count131072.C058548.packed 64 cuts58548 = true := by
 decide +kernel
def cuts58549 : List PrefixCut := [⟨30,98284005,98284059⟩,
⟨64,209874448,209874564⟩]
theorem checked58549 : checkPrefixCuts (2^48) 7678066689 10 Manual.Count131072.C058549.packed 64 cuts58549 = true := by
 decide +kernel
def pointBounds58549 : List (Nat × Nat × Nat) := [(7678128128,113614473100348,113614861335038)]
theorem point_links_checked58549 : (cuts58549.take 1).map (fun c => (7678066689-1+2*2^10*c.k,113614374816343+c.lower,113614763050979+c.upper)) = pointBounds58549 := by
 decide +kernel
def cuts58550 : List PrefixCut := [⟨64,212217046,212217167⟩]
theorem checked58550 : checkPrefixCuts (2^48) 7678197761 10 Manual.Count131072.C058550.packed 64 cuts58550 = true := by
 decide +kernel
def cuts58551 : List PrefixCut := [⟨20,64738481,64738519⟩,
⟨64,211626868,211626990⟩]
theorem checked58551 : checkPrefixCuts (2^48) 7678328833 10 Manual.Count131072.C058551.packed 64 cuts58551 = true := by
 decide +kernel
def pointBounds58551 : List (Nat × Nat × Nat) := [(7678369792,113614861646318,113615249881229)]
theorem point_links_checked58551 : (cuts58551.take 1).map (fun c => (7678328833-1+2*2^10*c.k,113614796907837+c.lower,113615185142710+c.upper)) = pointBounds58551 := by
 decide +kernel
def cuts58552 : List PrefixCut := [⟨64,211220037,211220158⟩]
theorem checked58552 : checkPrefixCuts (2^48) 7678459905 10 Manual.Count131072.C058552.packed 64 cuts58552 = true := by
 decide +kernel
def cuts58553 : List PrefixCut := [⟨10,33247949,33247968⟩,
⟨64,210153375,210153494⟩]
theorem checked58553 : checkPrefixCuts (2^48) 7678590977 10 Manual.Count131072.C058553.packed 64 cuts58553 = true := by
 decide +kernel
def pointBounds58553 : List (Nat × Nat × Nat) := [(7678611456,113615253002691,113615641237826)]
theorem point_links_checked58553 : (cuts58553.take 1).map (fun c => (7678590977-1+2*2^10*c.k,113615219754742+c.lower,113615607989858+c.upper)) = pointBounds58553 := by
 decide +kernel
def cuts58554 : List PrefixCut := [⟨64,208060399,208060522⟩]
theorem checked58554 : checkPrefixCuts (2^48) 7678722049 10 Manual.Count131072.C058554.packed 64 cuts58554 = true := by
 decide +kernel
def pointBounds58554 : List (Nat × Nat × Nat) := [(7678853120,113615637968516,113616026203874)]
theorem point_links_checked58554 : (cuts58554.take 1).map (fun c => (7678722049-1+2*2^10*c.k,113615429908117+c.lower,113615818143352+c.upper)) = pointBounds58554 := by
 decide +kernel
def cuts58555 : List PrefixCut := [⟨64,209706339,209706456⟩]
theorem checked58555 : checkPrefixCuts (2^48) 7678853121 10 Manual.Count131072.C058555.packed 64 cuts58555 = true := by
 decide +kernel
def cuts58556 : List PrefixCut := [⟨54,178363047,178363150⟩,
⟨64,210289247,210289369⟩]
theorem checked58556 : checkPrefixCuts (2^48) 7678984193 10 Manual.Count131072.C058556.packed 64 cuts58556 = true := by
 decide +kernel
def pointBounds58556 : List (Nat × Nat × Nat) := [(7679094784,113616026037902,113616414273480)]
theorem point_links_checked58556 : (cuts58556.take 1).map (fun c => (7678984193-1+2*2^10*c.k,113615847674855+c.lower,113616235910330+c.upper)) = pointBounds58556 := by
 decide +kernel
def cuts58557 : List PrefixCut := [⟨64,209992404,209992526⟩]
theorem checked58557 : checkPrefixCuts (2^48) 7679115265 10 Manual.Count131072.C058557.packed 64 cuts58557 = true := by
 decide +kernel
def cuts58558 : List PrefixCut := [⟨44,142619787,142619870⟩,
⟨64,209255754,209255874⟩]
theorem checked58558 : checkPrefixCuts (2^48) 7679246337 10 Manual.Count131072.C058558.packed 64 cuts58558 = true := by
 decide +kernel
def pointBounds58558 : List (Nat × Nat × Nat) := [(7679336448,113616410576293,113616798812095)]
theorem point_links_checked58558 : (cuts58558.take 1).map (fun c => (7679246337-1+2*2^10*c.k,113616267956506+c.lower,113616656192225+c.upper)) = pointBounds58558 := by
 decide +kernel
def cuts58559 : List PrefixCut := [⟨64,214713478,214713600⟩]
theorem checked58559 : checkPrefixCuts (2^48) 7679377409 10 Manual.Count131072.C058559.packed 64 cuts58559 = true := by
 decide +kernel
def cuts58560 : List PrefixCut := [⟨34,109701107,109701169⟩,
⟨64,208478902,208479017⟩]
theorem checked58560 : checkPrefixCuts (2^48) 7679508481 10 Manual.Count131072.C058560.packed 64 cuts58560 = true := by
 decide +kernel
def pointBounds58560 : List (Nat × Nat × Nat) := [(7679578112,113616801626845,113617189862868)]
theorem point_links_checked58560 : (cuts58560.take 1).map (fun c => (7679508481-1+2*2^10*c.k,113616691925738+c.lower,113617080161699+c.upper)) = pointBounds58560 := by
 decide +kernel
def cuts58561 : List PrefixCut := [⟨64,211993922,211994044⟩]
theorem checked58561 : checkPrefixCuts (2^48) 7679639553 10 Manual.Count131072.C058561.packed 64 cuts58561 = true := by
 decide +kernel
def cuts58562 : List PrefixCut := [⟨24,80889537,80889585⟩,
⟨64,214006122,214006244⟩]
theorem checked58562 : checkPrefixCuts (2^48) 7679770625 10 Manual.Count131072.C058562.packed 64 cuts58562 = true := by
 decide +kernel
def pointBounds58562 : List (Nat × Nat × Nat) := [(7679819776,113617193288099,113617581524345)]
theorem point_links_checked58562 : (cuts58562.take 1).map (fun c => (7679770625-1+2*2^10*c.k,113617112398562+c.lower,113617500634760+c.upper)) = pointBounds58562 := by
 decide +kernel
def cuts58563 : List PrefixCut := [⟨64,209604406,209604525⟩]
theorem checked58563 : checkPrefixCuts (2^48) 7679901697 10 Manual.Count131072.C058563.packed 64 cuts58563 = true := by
 decide +kernel
def cuts58564 : List PrefixCut := [⟨14,46728943,46728969⟩,
⟨64,209930664,209930784⟩]
theorem checked58564 : checkPrefixCuts (2^48) 7680032769 10 Manual.Count131072.C058564.packed 64 cuts58564 = true := by
 decide +kernel
def pointBounds58564 : List (Nat × Nat × Nat) := [(7680061440,113617582738033,113617970974498)]
theorem point_links_checked58564 : (cuts58564.take 1).map (fun c => (7680032769-1+2*2^10*c.k,113617536009090+c.lower,113617924245529+c.upper)) = pointBounds58564 := by
 decide +kernel
def cuts58565 : List PrefixCut := [⟨64,211099882,211100002⟩]
theorem checked58565 : checkPrefixCuts (2^48) 7680163841 10 Manual.Count131072.C058565.packed 64 cuts58565 = true := by
 decide +kernel
def cuts58566 : List PrefixCut := [⟨4,13486814,13486822⟩,
⟨64,208420916,208421038⟩]
theorem checked58566 : checkPrefixCuts (2^48) 7680294913 10 Manual.Count131072.C058566.packed 64 cuts58566 = true := by
 decide +kernel
def pointBounds58566 : List (Nat × Nat × Nat) := [(7680303104,113617970526450,113618358763137)]
theorem point_links_checked58566 : (cuts58566.take 1).map (fun c => (7680294913-1+2*2^10*c.k,113617957039636+c.lower,113618345276315+c.upper)) = pointBounds58566 := by
 decide +kernel
def cuts58567 : List PrefixCut := [⟨58,193171921,193172032⟩,
⟨64,212411988,212412110⟩]
theorem checked58567 : checkPrefixCuts (2^48) 7680425985 10 Manual.Count131072.C058567.packed 64 cuts58567 = true := by
 decide +kernel
def pointBounds58567 : List (Nat × Nat × Nat) := [(7680544768,113618358632473,113618746869385)]
theorem point_links_checked58567 : (cuts58567.take 1).map (fun c => (7680425985-1+2*2^10*c.k,113618165460552+c.lower,113618553697353+c.upper)) = pointBounds58567 := by
 decide +kernel
def cuts58568 : List PrefixCut := [⟨64,211418887,211419011⟩]
theorem checked58568 : checkPrefixCuts (2^48) 7680557057 10 Manual.Count131072.C058568.packed 64 cuts58568 = true := by
 decide +kernel
def cuts58569 : List PrefixCut := [⟨48,156628680,156628768⟩,
⟨64,209069887,209070005⟩]
theorem checked58569 : checkPrefixCuts (2^48) 7680688129 10 Manual.Count131072.C058569.packed 64 cuts58569 = true := by
 decide +kernel
def pointBounds58569 : List (Nat × Nat × Nat) := [(7680786432,113618745920107,113619134157242)]
theorem point_links_checked58569 : (cuts58569.take 1).map (fun c => (7680688129-1+2*2^10*c.k,113618589291427+c.lower,113618977528474+c.upper)) = pointBounds58569 := by
 decide +kernel
def cuts58570 : List PrefixCut := [⟨64,211191788,211191908⟩]
theorem checked58570 : checkPrefixCuts (2^48) 7680819201 10 Manual.Count131072.C058570.packed 64 cuts58570 = true := by
 decide +kernel
def cuts58571 : List PrefixCut := [⟨38,125144920,125144991⟩,
⟨64,210528572,210528688⟩]
theorem checked58571 : checkPrefixCuts (2^48) 7680950273 10 Manual.Count131072.C058571.packed 64 cuts58571 = true := by
 decide +kernel
def pointBounds58571 : List (Nat × Nat × Nat) := [(7681028096,113619134698022,113619522935378)]
theorem point_links_checked58571 : (cuts58571.take 1).map (fun c => (7680950273-1+2*2^10*c.k,113619009553102+c.lower,113619397790387+c.upper)) = pointBounds58571 := by
 decide +kernel
def cuts58572 : List PrefixCut := [⟨64,210121872,210121992⟩]
theorem checked58572 : checkPrefixCuts (2^48) 7681081345 10 Manual.Count131072.C058572.packed 64 cuts58572 = true := by
 decide +kernel
def cuts58573 : List PrefixCut := [⟨28,93040273,93040328⟩,
⟨64,210081669,210081789⟩]
theorem checked58573 : checkPrefixCuts (2^48) 7681212417 10 Manual.Count131072.C058573.packed 64 cuts58573 = true := by
 decide +kernel
def pointBounds58573 : List (Nat × Nat × Nat) := [(7681269760,113619523243819,113619911481395)]
theorem point_links_checked58573 : (cuts58573.take 1).map (fun c => (7681212417-1+2*2^10*c.k,113619430203546+c.lower,113619818441067+c.upper)) = pointBounds58573 := by
 decide +kernel
def cuts58574 : List PrefixCut := [⟨64,209381838,209381955⟩]
theorem checked58574 : checkPrefixCuts (2^48) 7681343489 10 Manual.Count131072.C058574.packed 64 cuts58574 = true := by
 decide +kernel
def cuts58575 : List PrefixCut := [⟨18,58922352,58922386⟩,
⟨64,209634769,209634891⟩]
theorem checked58575 : checkPrefixCuts (2^48) 7681474561 10 Manual.Count131072.C058575.packed 64 cuts58575 = true := by
 decide +kernel
def pointBounds58575 : List (Nat × Nat × Nat) := [(7681511424,113619908589405,113620296827197)]
theorem point_links_checked58575 : (cuts58575.take 1).map (fun c => (7681474561-1+2*2^10*c.k,113619849667053+c.lower,113620237904811+c.upper)) = pointBounds58575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000267
