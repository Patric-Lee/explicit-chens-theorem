import PlattAssemblyKernel
import PlattCertificates.Count131072.C036496
import PlattCertificates.Count131072.C036497
import PlattCertificates.Count131072.C036498
import PlattCertificates.Count131072.C036499
import PlattCertificates.Count131072.C036500
import PlattCertificates.Count131072.C036501
import PlattCertificates.Count131072.C036502
import PlattCertificates.Count131072.C036503
import PlattCertificates.Count131072.C036504
import PlattCertificates.Count131072.C036505
import PlattCertificates.Count131072.C036506
import PlattCertificates.Count131072.C036507
import PlattCertificates.Count131072.C036508
import PlattCertificates.Count131072.C036509
import PlattCertificates.Count131072.C036510
import PlattCertificates.Count131072.C036511
import PlattCertificates.Count131072.C036512
import PlattCertificates.Count131072.C036513
import PlattCertificates.Count131072.C036514
import PlattCertificates.Count131072.C036515
import PlattCertificates.Count131072.C036516
import PlattCertificates.Count131072.C036517
import PlattCertificates.Count131072.C036518
import PlattCertificates.Count131072.C036519
import PlattCertificates.Count131072.C036520
import PlattCertificates.Count131072.C036521
import PlattCertificates.Count131072.C036522
import PlattCertificates.Count131072.C036523
import PlattCertificates.Count131072.C036524
import PlattCertificates.Count131072.C036525
import PlattCertificates.Count131072.C036526
import PlattCertificates.Count131072.C036527
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000203
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36496 : List PrefixCut := [⟨51,273444509,273444681⟩,
⟨64,343289201,343289416⟩]
theorem checked36496 : checkPrefixCuts (2^48) 4787535873 10 Manual.Count131072.C036496.packed 64 cuts36496 = true := by
 decide +kernel
def pointBounds36496 : List (Nat × Nat × Nat) := [(4787640320,107712096976959,107712481786428)]
theorem point_links_checked36496 : (cuts36496.take 1).map (fun c => (4787535873-1+2*2^10*c.k,107711823532450+c.lower,107712208341747+c.upper)) = pointBounds36496 := by
 decide +kernel
def cuts36497 : List PrefixCut := [⟨61,327524044,327524248⟩,
⟨64,343279788,343280001⟩]
theorem checked36497 : checkPrefixCuts (2^48) 4787666945 10 Manual.Count131072.C036497.packed 64 cuts36497 = true := by
 decide +kernel
def pointBounds36497 : List (Nat × Nat × Nat) := [(4787791872,107712494345695,107712879155411)]
theorem point_links_checked36497 : (cuts36497.take 1).map (fun c => (4787666945-1+2*2^10*c.k,107712166821651+c.lower,107712551631163+c.upper)) = pointBounds36497 := by
 decide +kernel
def cuts36498 : List PrefixCut := [⟨64,344622565,344622772⟩]
theorem checked36498 : checkPrefixCuts (2^48) 4787798017 10 Manual.Count131072.C036498.packed 64 cuts36498 = true := by
 decide +kernel
def cuts36499 : List PrefixCut := [⟨7,38153641,38153664⟩,
⟨64,346847088,346847305⟩]
theorem checked36499 : checkPrefixCuts (2^48) 4787929089 10 Manual.Count131072.C036499.packed 64 cuts36499 = true := by
 decide +kernel
def pointBounds36499 : List (Nat × Nat × Nat) := [(4787943424,107712892877645,107713277687600)]
theorem point_links_checked36499 : (cuts36499.take 1).map (fun c => (4787929089-1+2*2^10*c.k,107712854724004+c.lower,107713239533936+c.upper)) = pointBounds36499 := by
 decide +kernel
def cuts36500 : List PrefixCut := [⟨17,91471983,91472042⟩,
⟨64,348130845,348131061⟩]
theorem checked36500 : checkPrefixCuts (2^48) 4788060161 10 Manual.Count131072.C036500.packed 64 cuts36500 = true := by
 decide +kernel
def pointBounds36500 : List (Nat × Nat × Nat) := [(4788094976,107713293043075,107713677853283)]
theorem point_links_checked36500 : (cuts36500.take 1).map (fun c => (4788060161-1+2*2^10*c.k,107713201571092+c.lower,107713586381241+c.upper)) = pointBounds36500 := by
 decide +kernel
def cuts36501 : List PrefixCut := [⟨27,140672229,140672315⟩,
⟨64,341419857,341420065⟩]
theorem checked36501 : checkPrefixCuts (2^48) 4788191233 10 Manual.Count131072.C036501.packed 64 cuts36501 = true := by
 decide +kernel
def pointBounds36501 : List (Nat × Nat × Nat) := [(4788246528,107713690374166,107714075184617)]
theorem point_links_checked36501 : (cuts36501.take 1).map (fun c => (4788191233-1+2*2^10*c.k,107713549701937+c.lower,107713934512302+c.upper)) = pointBounds36501 := by
 decide +kernel
def cuts36502 : List PrefixCut := [⟨37,199803907,199804029⟩,
⟨64,345525339,345525550⟩]
theorem checked36502 : checkPrefixCuts (2^48) 4788322305 10 Manual.Count131072.C036502.packed 64 cuts36502 = true := by
 decide +kernel
def pointBounds36502 : List (Nat × Nat × Nat) := [(4788398080,107714090925701,107714475736396)]
theorem point_links_checked36502 : (cuts36502.take 1).map (fun c => (4788322305-1+2*2^10*c.k,107713891121794+c.lower,107714275932367+c.upper)) = pointBounds36502 := by
 decide +kernel
def cuts36503 : List PrefixCut := [⟨47,255346463,255346622⟩,
⟨64,346044946,346045160⟩]
theorem checked36503 : checkPrefixCuts (2^48) 4788453377 10 Manual.Count131072.C036503.packed 64 cuts36503 = true := by
 decide +kernel
def pointBounds36503 : List (Nat × Nat × Nat) := [(4788549632,107714491993596,107714876804539)]
theorem point_links_checked36503 : (cuts36503.take 1).map (fun c => (4788453377-1+2*2^10*c.k,107714236647133+c.lower,107714621457917+c.upper)) = pointBounds36503 := by
 decide +kernel
def cuts36504 : List PrefixCut := [⟨57,305713099,305713288⟩,
⟨64,344801051,344801266⟩]
theorem checked36504 : checkPrefixCuts (2^48) 4788584449 10 Manual.Count131072.C036504.packed 64 cuts36504 = true := by
 decide +kernel
def pointBounds36504 : List (Nat × Nat × Nat) := [(4788701184,107714888405178,107715273216365)]
theorem point_links_checked36504 : (cuts36504.take 1).map (fun c => (4788584449-1+2*2^10*c.k,107714582692079+c.lower,107714967503077+c.upper)) = pointBounds36504 := by
 decide +kernel
def cuts36505 : List PrefixCut := [⟨64,351022094,351022309⟩]
theorem checked36505 : checkPrefixCuts (2^48) 4788715521 10 Manual.Count131072.C036505.packed 64 cuts36505 = true := by
 decide +kernel
def cuts36506 : List PrefixCut := [⟨3,16516376,16516387⟩,
⟨64,342960178,342960389⟩]
theorem checked36506 : checkPrefixCuts (2^48) 4788846593 10 Manual.Count131072.C036506.packed 64 cuts36506 = true := by
 decide +kernel
def pointBounds36506 : List (Nat × Nat × Nat) := [(4788852736,107715295031600,107715679843039)]
theorem point_links_checked36506 : (cuts36506.take 1).map (fun c => (4788846593-1+2*2^10*c.k,107715278515224+c.lower,107715663326652+c.upper)) = pointBounds36506 := by
 decide +kernel
def cuts36507 : List PrefixCut := [⟨13,70941916,70941960⟩,
⟨64,343362181,343362392⟩]
theorem checked36507 : checkPrefixCuts (2^48) 4788977665 10 Manual.Count131072.C036507.packed 64 cuts36507 = true := by
 decide +kernel
def pointBounds36507 : List (Nat × Nat × Nat) := [(4789004288,107715692417318,107716077229001)]
theorem point_links_checked36507 : (cuts36507.take 1).map (fun c => (4788977665-1+2*2^10*c.k,107715621475402+c.lower,107716006287041+c.upper)) = pointBounds36507 := by
 decide +kernel
def cuts36508 : List PrefixCut := [⟨23,123365943,123366021⟩,
⟨64,347995841,347996058⟩]
theorem checked36508 : checkPrefixCuts (2^48) 4789108737 10 Manual.Count131072.C036508.packed 64 cuts36508 = true := by
 decide +kernel
def pointBounds36508 : List (Nat × Nat × Nat) := [(4789155840,107716088203526,107716473015454)]
theorem point_links_checked36508 : (cuts36508.take 1).map (fun c => (4789108737-1+2*2^10*c.k,107715964837583+c.lower,107716349649433+c.upper)) = pointBounds36508 := by
 decide +kernel
def cuts36509 : List PrefixCut := [⟨33,175434219,175434325⟩,
⟨64,343813517,343813726⟩]
theorem checked36509 : checkPrefixCuts (2^48) 4789239809 10 Manual.Count131072.C036509.packed 64 cuts36509 = true := by
 decide +kernel
def pointBounds36509 : List (Nat × Nat × Nat) := [(4789307392,107716488267643,107716873079816)]
theorem point_links_checked36509 : (cuts36509.take 1).map (fun c => (4789239809-1+2*2^10*c.k,107716312833424+c.lower,107716697645491+c.upper)) = pointBounds36509 := by
 decide +kernel
def cuts36510 : List PrefixCut := [⟨43,233670352,233670493⟩,
⟨64,347154063,347154273⟩]
theorem checked36510 : checkPrefixCuts (2^48) 4789370881 10 Manual.Count131072.C036510.packed 64 cuts36510 = true := by
 decide +kernel
def pointBounds36510 : List (Nat × Nat × Nat) := [(4789458944,107716890317293,107717275129710)]
theorem point_links_checked36510 : (cuts36510.take 1).map (fun c => (4789370881-1+2*2^10*c.k,107716656646941+c.lower,107717041459217+c.upper)) = pointBounds36510 := by
 decide +kernel
def cuts36511 : List PrefixCut := [⟨53,283557838,283558016⟩,
⟨64,342031663,342031878⟩]
theorem checked36511 : checkPrefixCuts (2^48) 4789501953 10 Manual.Count131072.C036511.packed 64 cuts36511 = true := by
 decide +kernel
def pointBounds36511 : List (Nat × Nat × Nat) := [(4789610496,107717287358842,107717672171506)]
theorem point_links_checked36511 : (cuts36511.take 1).map (fun c => (4789501953-1+2*2^10*c.k,107717003801004+c.lower,107717388613490+c.upper)) = pointBounds36511 := by
 decide +kernel
def cuts36512 : List PrefixCut := [⟨63,347664020,347664226⟩,
⟨64,353481847,353482057⟩]
theorem checked36512 : checkPrefixCuts (2^48) 4789633025 10 Manual.Count131072.C036512.packed 64 cuts36512 = true := by
 decide +kernel
def pointBounds36512 : List (Nat × Nat × Nat) := [(4789762048,107717693496687,107718078309594)]
theorem point_links_checked36512 : (cuts36512.take 1).map (fun c => (4789633025-1+2*2^10*c.k,107717345832667+c.lower,107717730645368+c.upper)) = pointBounds36512 := by
 decide +kernel
def cuts36513 : List PrefixCut := [⟨64,349064763,349064977⟩]
theorem checked36513 : checkPrefixCuts (2^48) 4789764097 10 Manual.Count131072.C036513.packed 64 cuts36513 = true := by
 decide +kernel
def cuts36514 : List PrefixCut := [⟨9,50067096,50067126⟩,
⟨64,345118089,345118306⟩]
theorem checked36514 : checkPrefixCuts (2^48) 4789895169 10 Manual.Count131072.C036514.packed 64 cuts36514 = true := by
 decide +kernel
def pointBounds36514 : List (Nat × Nat × Nat) := [(4789913600,107718098446373,107718483259528)]
theorem point_links_checked36514 : (cuts36514.take 1).map (fun c => (4789895169-1+2*2^10*c.k,107718048379277+c.lower,107718433192402+c.upper)) = pointBounds36514 := by
 decide +kernel
def cuts36515 : List PrefixCut := [⟨19,105184813,105184876⟩,
⟨64,349633319,349633534⟩]
theorem checked36515 : checkPrefixCuts (2^48) 4790026241 10 Manual.Count131072.C036515.packed 64 cuts36515 = true := by
 decide +kernel
def pointBounds36515 : List (Nat × Nat × Nat) := [(4790065152,107718498682179,107718883495584)]
theorem point_links_checked36515 : (cuts36515.take 1).map (fun c => (4790026241-1+2*2^10*c.k,107718393497366+c.lower,107718778310708+c.upper)) = pointBounds36515 := by
 decide +kernel
def cuts36516 : List PrefixCut := [⟨29,156068490,156068586⟩,
⟨64,343747717,343747922⟩]
theorem checked36516 : checkPrefixCuts (2^48) 4790157313 10 Manual.Count131072.C036516.packed 64 cuts36516 = true := by
 decide +kernel
def pointBounds36516 : List (Nat × Nat × Nat) := [(4790216704,107718899199175,107719284012828)]
theorem point_links_checked36516 : (cuts36516.take 1).map (fun c => (4790157313-1+2*2^10*c.k,107718743130685+c.lower,107719127944242+c.upper)) = pointBounds36516 := by
 decide +kernel
def cuts36517 : List PrefixCut := [⟨39,207419289,207419420⟩,
⟨64,344913459,344913674⟩]
theorem checked36517 : checkPrefixCuts (2^48) 4790288385 10 Manual.Count131072.C036517.packed 64 cuts36517 = true := by
 decide +kernel
def pointBounds36517 : List (Nat × Nat × Nat) := [(4790368256,107719294297691,107719679111584)]
theorem point_links_checked36517 : (cuts36517.take 1).map (fun c => (4790288385-1+2*2^10*c.k,107719086878402+c.lower,107719471692164+c.upper)) = pointBounds36517 := by
 decide +kernel
def cuts36518 : List PrefixCut := [⟨49,259354583,259354740⟩,
⟨64,340791037,340791243⟩]
theorem checked36518 : checkPrefixCuts (2^48) 4790419457 10 Manual.Count131072.C036518.packed 64 cuts36518 = true := by
 decide +kernel
def pointBounds36518 : List (Nat × Nat × Nat) := [(4790519808,107719691146444,107720075960578)]
theorem point_links_checked36518 : (cuts36518.take 1).map (fun c => (4790419457-1+2*2^10*c.k,107719431791861+c.lower,107719816605838+c.upper)) = pointBounds36518 := by
 decide +kernel
def cuts36519 : List PrefixCut := [⟨59,317632416,317632608⟩,
⟨64,343366986,343367195⟩]
theorem checked36519 : checkPrefixCuts (2^48) 4790550529 10 Manual.Count131072.C036519.packed 64 cuts36519 = true := by
 decide +kernel
def pointBounds36519 : List (Nat × Nat × Nat) := [(4790671360,107720090215314,107720475029689)]
theorem point_links_checked36519 : (cuts36519.take 1).map (fun c => (4790550529-1+2*2^10*c.k,107719772582898+c.lower,107720157397081+c.upper)) = pointBounds36519 := by
 decide +kernel
def cuts36520 : List PrefixCut := [⟨64,347705351,347705561⟩]
theorem checked36520 : checkPrefixCuts (2^48) 4790681601 10 Manual.Count131072.C036520.packed 64 cuts36520 = true := by
 decide +kernel
def cuts36521 : List PrefixCut := [⟨5,27437648,27437665⟩,
⟨64,343818166,343818384⟩]
theorem checked36521 : checkPrefixCuts (2^48) 4790812673 10 Manual.Count131072.C036521.packed 64 cuts36521 = true := by
 decide +kernel
def pointBounds36521 : List (Nat × Nat × Nat) := [(4790822912,107720491092883,107720875907502)]
theorem point_links_checked36521 : (cuts36521.take 1).map (fun c => (4790812673-1+2*2^10*c.k,107720463655235+c.lower,107720848469837+c.upper)) = pointBounds36521 := by
 decide +kernel
def cuts36522 : List PrefixCut := [⟨15,80724235,80724282⟩,
⟨64,346158791,346158998⟩]
theorem checked36522 : checkPrefixCuts (2^48) 4790943745 10 Manual.Count131072.C036522.packed 64 cuts36522 = true := by
 decide +kernel
def pointBounds36522 : List (Nat × Nat × Nat) := [(4790974464,107720888197636,107721273012503)]
theorem point_links_checked36522 : (cuts36522.take 1).map (fun c => (4790943745-1+2*2^10*c.k,107720807473401+c.lower,107721192288221+c.upper)) = pointBounds36522 := by
 decide +kernel
def cuts36523 : List PrefixCut := [⟨25,133361424,133361508⟩,
⟨64,345620571,345620782⟩]
theorem checked36523 : checkPrefixCuts (2^48) 4791074817 10 Manual.Count131072.C036523.packed 64 cuts36523 = true := by
 decide +kernel
def pointBounds36523 : List (Nat × Nat × Nat) := [(4791126016,107721286993616,107721671808727)]
theorem point_links_checked36523 : (cuts36523.take 1).map (fun c => (4791074817-1+2*2^10*c.k,107721153632192+c.lower,107721538447219+c.upper)) = pointBounds36523 := by
 decide +kernel
def cuts36524 : List PrefixCut := [⟨35,189109155,189109269⟩,
⟨64,343731228,343731439⟩]
theorem checked36524 : checkPrefixCuts (2^48) 4791205889 10 Manual.Count131072.C036524.packed 64 cuts36524 = true := by
 decide +kernel
def pointBounds36524 : List (Nat × Nat × Nat) := [(4791277568,107721688361918,107722073177270)]
theorem point_links_checked36524 : (cuts36524.take 1).map (fun c => (4791205889-1+2*2^10*c.k,107721499252763+c.lower,107721884068001+c.upper)) = pointBounds36524 := by
 decide +kernel
def cuts36525 : List PrefixCut := [⟨45,243443681,243443828⟩,
⟨64,343486857,343487068⟩]
theorem checked36525 : checkPrefixCuts (2^48) 4791336961 10 Manual.Count131072.C036525.packed 64 cuts36525 = true := by
 decide +kernel
def pointBounds36525 : List (Nat × Nat × Nat) := [(4791429120,107722086427672,107722471243268)]
theorem point_links_checked36525 : (cuts36525.take 1).map (fun c => (4791336961-1+2*2^10*c.k,107721842983991+c.lower,107722227799440+c.upper)) = pointBounds36525 := by
 decide +kernel
def cuts36526 : List PrefixCut := [⟨55,296893853,296894033⟩,
⟨64,348118209,348118418⟩]
theorem checked36526 : checkPrefixCuts (2^48) 4791468033 10 Manual.Count131072.C036526.packed 64 cuts36526 = true := by
 decide +kernel
def pointBounds36526 : List (Nat × Nat × Nat) := [(4791580672,107722483364701,107722868180541)]
theorem point_links_checked36526 : (cuts36526.take 1).map (fun c => (4791468033-1+2*2^10*c.k,107722186470848+c.lower,107722571286508+c.upper)) = pointBounds36526 := by
 decide +kernel
def cuts36527 : List PrefixCut := [⟨64,343879252,343879466⟩]
theorem checked36527 : checkPrefixCuts (2^48) 4791599105 10 Manual.Count131072.C036527.packed 64 cuts36527 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000203
