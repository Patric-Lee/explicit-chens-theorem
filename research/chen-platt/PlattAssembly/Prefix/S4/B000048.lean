import PlattAssemblyKernel
import PlattCertificates.Count131072.C031536
import PlattCertificates.Count131072.C031537
import PlattCertificates.Count131072.C031538
import PlattCertificates.Count131072.C031539
import PlattCertificates.Count131072.C031540
import PlattCertificates.Count131072.C031541
import PlattCertificates.Count131072.C031542
import PlattCertificates.Count131072.C031543
import PlattCertificates.Count131072.C031544
import PlattCertificates.Count131072.C031545
import PlattCertificates.Count131072.C031546
import PlattCertificates.Count131072.C031547
import PlattCertificates.Count131072.C031548
import PlattCertificates.Count131072.C031549
import PlattCertificates.Count131072.C031550
import PlattCertificates.Count131072.C031551
import PlattCertificates.Count131072.C031552
import PlattCertificates.Count131072.C031553
import PlattCertificates.Count131072.C031554
import PlattCertificates.Count131072.C031555
import PlattCertificates.Count131072.C031556
import PlattCertificates.Count131072.C031557
import PlattCertificates.Count131072.C031558
import PlattCertificates.Count131072.C031559
import PlattCertificates.Count131072.C031560
import PlattCertificates.Count131072.C031561
import PlattCertificates.Count131072.C031562
import PlattCertificates.Count131072.C031563
import PlattCertificates.Count131072.C031564
import PlattCertificates.Count131072.C031565
import PlattCertificates.Count131072.C031566
import PlattCertificates.Count131072.C031567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts31536 : List PrefixCut := [⟨33,101706712,101706770⟩,
⟨128,400631245,400631466⟩]
theorem checked31536 : checkPrefixCuts (2^48) 4137418753 9 Manual.Count131072.C031536.packed 128 cuts31536 = true := by
 decide +kernel
def pointBounds31536 : List (Nat × Nat × Nat) := [(4137452544,105862873045266,105863256724039)]
theorem point_links_checked31536 : (cuts31536.take 1).map (fun c => (4137418753-1+2*2^9*c.k,105862771338554+c.lower,105863155017269+c.upper)) = pointBounds31536 := by
 decide +kernel
def cuts31537 : List PrefixCut := [⟨32,102247736,102247793⟩,
⟨128,405312533,405312763⟩]
theorem checked31537 : checkPrefixCuts (2^48) 4137549825 9 Manual.Count131072.C031537.packed 128 cuts31537 = true := by
 decide +kernel
def pointBounds31537 : List (Nat × Nat × Nat) := [(4137582592,105863274217535,105863657896528)]
theorem point_links_checked31537 : (cuts31537.take 1).map (fun c => (4137549825-1+2*2^9*c.k,105863171969799+c.lower,105863555648735+c.upper)) = pointBounds31537 := by
 decide +kernel
def cuts31538 : List PrefixCut := [⟨31,94489434,94489487⟩,
⟨128,398088900,398089129⟩]
theorem checked31538 : checkPrefixCuts (2^48) 4137680897 9 Manual.Count131072.C031538.packed 128 cuts31538 = true := by
 decide +kernel
def pointBounds31538 : List (Nat × Nat × Nat) := [(4137712640,105863671771766,105864055450985)]
theorem point_links_checked31538 : (cuts31538.take 1).map (fun c => (4137680897-1+2*2^9*c.k,105863577282332+c.lower,105863960961498+c.upper)) = pointBounds31538 := by
 decide +kernel
def cuts31539 : List PrefixCut := [⟨30,97547571,97547626⟩,
⟨128,405422950,405423180⟩]
theorem checked31539 : checkPrefixCuts (2^48) 4137811969 9 Manual.Count131072.C031539.packed 128 cuts31539 = true := by
 decide +kernel
def pointBounds31539 : List (Nat × Nat × Nat) := [(4137842688,105864072918803,105864456598253)]
theorem point_links_checked31539 : (cuts31539.take 1).map (fun c => (4137811969-1+2*2^9*c.k,105863975371232+c.lower,105864359050627+c.upper)) = pointBounds31539 := by
 decide +kernel
def cuts31540 : List PrefixCut := [⟨29,92306744,92306796⟩,
⟨128,404049661,404049884⟩]
theorem checked31540 : checkPrefixCuts (2^48) 4137943041 9 Manual.Count131072.C031540.packed 128 cuts31540 = true := by
 decide +kernel
def pointBounds31540 : List (Nat × Nat × Nat) := [(4137972736,105864473100926,105864856780603)]
theorem point_links_checked31540 : (cuts31540.take 1).map (fun c => (4137943041-1+2*2^9*c.k,105864380794182+c.lower,105864764473807+c.upper)) = pointBounds31540 := by
 decide +kernel
def cuts31541 : List PrefixCut := [⟨28,90263220,90263268⟩,
⟨128,405397293,405397527⟩]
theorem checked31541 : checkPrefixCuts (2^48) 4138074113 9 Manual.Count131072.C031541.packed 128 cuts31541 = true := by
 decide +kernel
def pointBounds31541 : List (Nat × Nat × Nat) := [(4138102784,105864875107063,105865258786959)]
theorem point_links_checked31541 : (cuts31541.take 1).map (fun c => (4138074113-1+2*2^9*c.k,105864784843843+c.lower,105865168523691+c.upper)) = pointBounds31541 := by
 decide +kernel
def cuts31542 : List PrefixCut := [⟨27,87063508,87063554⟩,
⟨128,406812731,406812954⟩]
theorem checked31542 : checkPrefixCuts (2^48) 4138205185 9 Manual.Count131072.C031542.packed 128 cuts31542 = true := by
 decide +kernel
def pointBounds31542 : List (Nat × Nat × Nat) := [(4138232832,105865277304644,105865660984772)]
theorem point_links_checked31542 : (cuts31542.take 1).map (fun c => (4138205185-1+2*2^9*c.k,105865190241136+c.lower,105865573921218+c.upper)) = pointBounds31542 := by
 decide +kernel
def cuts31543 : List PrefixCut := [⟨26,81687478,81687526⟩,
⟨128,398842088,398842307⟩]
theorem checked31543 : checkPrefixCuts (2^48) 4138336257 9 Manual.Count131072.C031543.packed 128 cuts31543 = true := by
 decide +kernel
def pointBounds31543 : List (Nat × Nat × Nat) := [(4138362880,105865678741345,105866062421698)]
theorem point_links_checked31543 : (cuts31543.take 1).map (fun c => (4138336257-1+2*2^9*c.k,105865597053867+c.lower,105865980734172+c.upper)) = pointBounds31543 := by
 decide +kernel
def cuts31544 : List PrefixCut := [⟨25,79168391,79168438⟩,
⟨128,401278004,401278239⟩]
theorem checked31544 : checkPrefixCuts (2^48) 4138467329 9 Manual.Count131072.C031544.packed 128 cuts31544 = true := by
 decide +kernel
def pointBounds31544 : List (Nat × Nat × Nat) := [(4138492928,105866075064346,105866458744917)]
theorem point_links_checked31544 : (cuts31544.take 1).map (fun c => (4138467329-1+2*2^9*c.k,105865995895955+c.lower,105866379576479+c.upper)) = pointBounds31544 := by
 decide +kernel
def cuts31545 : List PrefixCut := [⟨24,78621786,78621830⟩,
⟨128,407318253,407318478⟩]
theorem checked31545 : checkPrefixCuts (2^48) 4138598401 9 Manual.Count131072.C031545.packed 128 cuts31545 = true := by
 decide +kernel
def pointBounds31545 : List (Nat × Nat × Nat) := [(4138622976,105866475795745,105866859476548)]
theorem point_links_checked31545 : (cuts31545.take 1).map (fun c => (4138598401-1+2*2^9*c.k,105866397173959+c.lower,105866780854718+c.upper)) = pointBounds31545 := by
 decide +kernel
def cuts31546 : List PrefixCut := [⟨23,69574009,69574046⟩,
⟨128,396899859,396900083⟩]
theorem checked31546 : checkPrefixCuts (2^48) 4138729473 9 Manual.Count131072.C031546.packed 128 cuts31546 = true := by
 decide +kernel
def pointBounds31546 : List (Nat × Nat × Nat) := [(4138753024,105866874066221,105867257747242)]
theorem point_links_checked31546 : (cuts31546.take 1).map (fun c => (4138729473-1+2*2^9*c.k,105866804492212+c.lower,105867188173196+c.upper)) = pointBounds31546 := by
 decide +kernel
def cuts31547 : List PrefixCut := [⟨22,68687714,68687756⟩,
⟨128,404096061,404096295⟩]
theorem checked31547 : checkPrefixCuts (2^48) 4138860545 9 Manual.Count131072.C031547.packed 128 cuts31547 = true := by
 decide +kernel
def pointBounds31547 : List (Nat × Nat × Nat) := [(4138883072,105867270079785,105867653761035)]
theorem point_links_checked31547 : (cuts31547.take 1).map (fun c => (4138860545-1+2*2^9*c.k,105867201392071+c.lower,105867585073279+c.upper)) = pointBounds31547 := by
 decide +kernel
def cuts31548 : List PrefixCut := [⟨21,67869483,67869518⟩,
⟨128,402383191,402383417⟩]
theorem checked31548 : checkPrefixCuts (2^48) 4138991617 9 Manual.Count131072.C031548.packed 128 cuts31548 = true := by
 decide +kernel
def pointBounds31548 : List (Nat × Nat × Nat) := [(4139013120,105867673357615,105868057039092)]
theorem point_links_checked31548 : (cuts31548.take 1).map (fun c => (4138991617-1+2*2^9*c.k,105867605488132+c.lower,105867989169574+c.upper)) = pointBounds31548 := by
 decide +kernel
def cuts31549 : List PrefixCut := [⟨20,63243113,63243147⟩,
⟨128,396318219,396318449⟩]
theorem checked31549 : checkPrefixCuts (2^48) 4139122689 9 Manual.Count131072.C031549.packed 128 cuts31549 = true := by
 decide +kernel
def pointBounds31549 : List (Nat × Nat × Nat) := [(4139143168,105868071114436,105868454796138)]
theorem point_links_checked31549 : (cuts31549.take 1).map (fun c => (4139122689-1+2*2^9*c.k,105868007871323+c.lower,105868391552991+c.upper)) = pointBounds31549 := by
 decide +kernel
def cuts31550 : List PrefixCut := [⟨19,58957041,58957075⟩,
⟨128,400521699,400521927⟩]
theorem checked31550 : checkPrefixCuts (2^48) 4139253761 9 Manual.Count131072.C031550.packed 128 cuts31550 = true := by
 decide +kernel
def pointBounds31550 : List (Nat × Nat × Nat) := [(4139273216,105868463146583,105868846828515)]
theorem point_links_checked31550 : (cuts31550.take 1).map (fun c => (4139253761-1+2*2^9*c.k,105868404189542+c.lower,105868787871440+c.upper)) = pointBounds31550 := by
 decide +kernel
def cuts31551 : List PrefixCut := [⟨18,58139189,58139223⟩,
⟨128,402276943,402277170⟩]
theorem checked31551 : checkPrefixCuts (2^48) 4139384833 9 Manual.Count131072.C031551.packed 128 cuts31551 = true := by
 decide +kernel
def pointBounds31551 : List (Nat × Nat × Nat) := [(4139403264,105868862850430,105869246532590)]
theorem point_links_checked31551 : (cuts31551.take 1).map (fun c => (4139384833-1+2*2^9*c.k,105868804711241+c.lower,105869188393367+c.upper)) = pointBounds31551 := by
 decide +kernel
def cuts31552 : List PrefixCut := [⟨17,50589704,50589732⟩,
⟨128,396824518,396824751⟩]
theorem checked31552 : checkPrefixCuts (2^48) 4139515905 9 Manual.Count131072.C031552.packed 128 cuts31552 = true := by
 decide +kernel
def pointBounds31552 : List (Nat × Nat × Nat) := [(4139533312,105869257577888,105869641260269)]
theorem point_links_checked31552 : (cuts31552.take 1).map (fun c => (4139515905-1+2*2^9*c.k,105869206988184+c.lower,105869590670537+c.upper)) = pointBounds31552 := by
 decide +kernel
def cuts31553 : List PrefixCut := [⟨16,50452119,50452147⟩,
⟨128,400823641,400823866⟩]
theorem checked31553 : checkPrefixCuts (2^48) 4139646977 9 Manual.Count131072.C031553.packed 128 cuts31553 = true := by
 decide +kernel
def pointBounds31553 : List (Nat × Nat × Nat) := [(4139663360,105869654264821,105870037947435)]
theorem point_links_checked31553 : (cuts31553.take 1).map (fun c => (4139646977-1+2*2^9*c.k,105869603812702+c.lower,105869987495288+c.upper)) = pointBounds31553 := by
 decide +kernel
def cuts31554 : List PrefixCut := [⟨15,47866804,47866832⟩,
⟨128,402510719,402510941⟩]
theorem checked31554 : checkPrefixCuts (2^48) 4139778049 9 Manual.Count131072.C031554.packed 128 cuts31554 = true := by
 decide +kernel
def pointBounds31554 : List (Nat × Nat × Nat) := [(4139793408,105870052503147,105870436185986)]
theorem point_links_checked31554 : (cuts31554.take 1).map (fun c => (4139778049-1+2*2^9*c.k,105870004636343+c.lower,105870388319154+c.upper)) = pointBounds31554 := by
 decide +kernel
def cuts31555 : List PrefixCut := [⟨14,41542184,41542207⟩,
⟨128,403109827,403110049⟩]
theorem checked31555 : checkPrefixCuts (2^48) 4139909121 9 Manual.Count131072.C031555.packed 128 cuts31555 = true := by
 decide +kernel
def pointBounds31555 : List (Nat × Nat × Nat) := [(4139923456,105870448689246,105870832372302)]
theorem point_links_checked31555 : (cuts31555.take 1).map (fun c => (4139909121-1+2*2^9*c.k,105870407147062+c.lower,105870790830095+c.upper)) = pointBounds31555 := by
 decide +kernel
def cuts31556 : List PrefixCut := [⟨13,40045129,40045154⟩,
⟨128,401669366,401669600⟩]
theorem checked31556 : checkPrefixCuts (2^48) 4140040193 9 Manual.Count131072.C031556.packed 128 cuts31556 = true := by
 decide +kernel
def pointBounds31556 : List (Nat × Nat × Nat) := [(4140053504,105870850302018,105871233985298)]
theorem point_links_checked31556 : (cuts31556.take 1).map (fun c => (4140040193-1+2*2^9*c.k,105870810256889+c.lower,105871193940144+c.upper)) = pointBounds31556 := by
 decide +kernel
def cuts31557 : List PrefixCut := [⟨12,38208238,38208261⟩,
⟨128,399617102,399617330⟩]
theorem checked31557 : checkPrefixCuts (2^48) 4140171265 9 Manual.Count131072.C031557.packed 128 cuts31557 = true := by
 decide +kernel
def pointBounds31557 : List (Nat × Nat × Nat) := [(4140183552,105871250134493,105871633818005)]
theorem point_links_checked31557 : (cuts31557.take 1).map (fun c => (4140171265-1+2*2^9*c.k,105871211926255+c.lower,105871595609744+c.upper)) = pointBounds31557 := by
 decide +kernel
def cuts31558 : List PrefixCut := [⟨11,35487673,35487693⟩,
⟨128,401575961,401576187⟩]
theorem checked31558 : checkPrefixCuts (2^48) 4140302337 9 Manual.Count131072.C031558.packed 128 cuts31558 = true := by
 decide +kernel
def pointBounds31558 : List (Nat × Nat × Nat) := [(4140313600,105871647031030,105872030714767)]
theorem point_links_checked31558 : (cuts31558.take 1).map (fun c => (4140302337-1+2*2^9*c.k,105871611543357+c.lower,105871995227074+c.upper)) = pointBounds31558 := by
 decide +kernel
def cuts31559 : List PrefixCut := [⟨10,31203693,31203712⟩,
⟨128,402650894,402651127⟩]
theorem checked31559 : checkPrefixCuts (2^48) 4140433409 9 Manual.Count131072.C031559.packed 128 cuts31559 = true := by
 decide +kernel
def pointBounds31559 : List (Nat × Nat × Nat) := [(4140443648,105872044323011,105872428006973)]
theorem point_links_checked31559 : (cuts31559.take 1).map (fun c => (4140433409-1+2*2^9*c.k,105872013119318+c.lower,105872396803261+c.upper)) = pointBounds31559 := by
 decide +kernel
def cuts31560 : List PrefixCut := [⟨9,27803720,27803737⟩,
⟨128,407396683,407396916⟩]
theorem checked31560 : checkPrefixCuts (2^48) 4140564481 9 Manual.Count131072.C031560.packed 128 cuts31560 = true := by
 decide +kernel
def pointBounds31560 : List (Nat × Nat × Nat) := [(4140573696,105872443573932,105872827258125)]
theorem point_links_checked31560 : (cuts31560.take 1).map (fun c => (4140564481-1+2*2^9*c.k,105872415770212+c.lower,105872799454388+c.upper)) = pointBounds31560 := by
 decide +kernel
def cuts31561 : List PrefixCut := [⟨8,24539919,24539935⟩,
⟨128,404392818,404393043⟩]
theorem checked31561 : checkPrefixCuts (2^48) 4140695553 9 Manual.Count131072.C031561.packed 128 cuts31561 = true := by
 decide +kernel
def pointBounds31561 : List (Nat × Nat × Nat) := [(4140703744,105872847706814,105873231391239)]
theorem point_links_checked31561 : (cuts31561.take 1).map (fun c => (4140695553-1+2*2^9*c.k,105872823166895+c.lower,105873206851304+c.upper)) = pointBounds31561 := by
 decide +kernel
def cuts31562 : List PrefixCut := [⟨7,21888103,21888116⟩,
⟨128,399553864,399554093⟩]
theorem checked31562 : checkPrefixCuts (2^48) 4140826625 9 Manual.Count131072.C031562.packed 128 cuts31562 = true := by
 decide +kernel
def pointBounds31562 : List (Nat × Nat × Nat) := [(4140833792,105873249447816,105873633132463)]
theorem point_links_checked31562 : (cuts31562.take 1).map (fun c => (4140826625-1+2*2^9*c.k,105873227559713+c.lower,105873611244347+c.upper)) = pointBounds31562 := by
 decide +kernel
def cuts31563 : List PrefixCut := [⟨6,19916187,19916197⟩,
⟨128,401852257,401852488⟩]
theorem checked31563 : checkPrefixCuts (2^48) 4140957697 9 Manual.Count131072.C031563.packed 128 cuts31563 = true := by
 decide +kernel
def pointBounds31563 : List (Nat × Nat × Nat) := [(4140963840,105873647029764,105874030714637)]
theorem point_links_checked31563 : (cuts31563.take 1).map (fun c => (4140957697-1+2*2^9*c.k,105873627113577+c.lower,105874010798440+c.upper)) = pointBounds31563 := by
 decide +kernel
def cuts31564 : List PrefixCut := [⟨5,14002065,14002074⟩,
⟨128,398576934,398577168⟩]
theorem checked31564 : checkPrefixCuts (2^48) 4141088769 9 Manual.Count131072.C031564.packed 128 cuts31564 = true := by
 decide +kernel
def pointBounds31564 : List (Nat × Nat × Nat) := [(4141093888,105874042967899,105874426653002)]
theorem point_links_checked31564 : (cuts31564.take 1).map (fun c => (4141088769-1+2*2^9*c.k,105874028965834+c.lower,105874412650928+c.upper)) = pointBounds31564 := by
 decide +kernel
def cuts31565 : List PrefixCut := [⟨4,13797716,13797724⟩,
⟨128,401079227,401079467⟩]
theorem checked31565 : checkPrefixCuts (2^48) 4141219841 9 Manual.Count131072.C031565.packed 128 cuts31565 = true := by
 decide +kernel
def pointBounds31565 : List (Nat × Nat × Nat) := [(4141223936,105874441340484,105874825025820)]
theorem point_links_checked31565 : (cuts31565.take 1).map (fun c => (4141219841-1+2*2^9*c.k,105874427542768+c.lower,105874811228096+c.upper)) = pointBounds31565 := by
 decide +kernel
def cuts31566 : List PrefixCut := [⟨3,9719267,9719273⟩,
⟨128,401814124,401814349⟩]
theorem checked31566 : checkPrefixCuts (2^48) 4141350913 9 Manual.Count131072.C031566.packed 128 cuts31566 = true := by
 decide +kernel
def pointBounds31566 : List (Nat × Nat × Nat) := [(4141353984,105874838341262,105875222026836)]
theorem point_links_checked31566 : (cuts31566.take 1).map (fun c => (4141350913-1+2*2^9*c.k,105874828621995+c.lower,105875212307563+c.upper)) = pointBounds31566 := by
 decide +kernel
def cuts31567 : List PrefixCut := [⟨2,6592582,6592586⟩,
⟨128,398199265,398199484⟩]
theorem checked31567 : checkPrefixCuts (2^48) 4141481985 9 Manual.Count131072.C031567.packed 128 cuts31567 = true := by
 decide +kernel
def pointBounds31567 : List (Nat × Nat × Nat) := [(4141484032,105875237028701,105875620714498)]
theorem point_links_checked31567 : (cuts31567.take 1).map (fun c => (4141481985-1+2*2^9*c.k,105875230436119+c.lower,105875614121912+c.upper)) = pointBounds31567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000048
