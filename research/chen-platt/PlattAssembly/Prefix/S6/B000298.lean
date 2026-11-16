import PlattAssemblyKernel
import PlattCertificates.Count131072.C059536
import PlattCertificates.Count131072.C059537
import PlattCertificates.Count131072.C059538
import PlattCertificates.Count131072.C059539
import PlattCertificates.Count131072.C059540
import PlattCertificates.Count131072.C059541
import PlattCertificates.Count131072.C059542
import PlattCertificates.Count131072.C059543
import PlattCertificates.Count131072.C059544
import PlattCertificates.Count131072.C059545
import PlattCertificates.Count131072.C059546
import PlattCertificates.Count131072.C059547
import PlattCertificates.Count131072.C059548
import PlattCertificates.Count131072.C059549
import PlattCertificates.Count131072.C059550
import PlattCertificates.Count131072.C059551
import PlattCertificates.Count131072.C059552
import PlattCertificates.Count131072.C059553
import PlattCertificates.Count131072.C059554
import PlattCertificates.Count131072.C059555
import PlattCertificates.Count131072.C059556
import PlattCertificates.Count131072.C059557
import PlattCertificates.Count131072.C059558
import PlattCertificates.Count131072.C059559
import PlattCertificates.Count131072.C059560
import PlattCertificates.Count131072.C059561
import PlattCertificates.Count131072.C059562
import PlattCertificates.Count131072.C059563
import PlattCertificates.Count131072.C059564
import PlattCertificates.Count131072.C059565
import PlattCertificates.Count131072.C059566
import PlattCertificates.Count131072.C059567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000298
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59536 : List PrefixCut := [⟨64,208559987,208560101⟩]
theorem checked59536 : checkPrefixCuts (2^48) 7807434753 10 Manual.Count131072.C059536.packed 64 cuts59536 = true := by
 decide +kernel
def cuts59537 : List PrefixCut := [⟨31,97699319,97699376⟩,
⟨64,204662950,204663067⟩]
theorem checked59537 : checkPrefixCuts (2^48) 7807565825 10 Manual.Count131072.C059537.packed 64 cuts59537 = true := by
 decide +kernel
def pointBounds59537 : List (Nat × Nat × Nat) := [(7807629312,113821206663658,113821595016348)]
theorem point_links_checked59537 : (cuts59537.take 1).map (fun c => (7807565825-1+2*2^10*c.k,113821108964339+c.lower,113821497316972+c.upper)) = pointBounds59537 := by
 decide +kernel
def cuts59538 : List PrefixCut := [⟨64,207579634,207579753⟩]
theorem checked59538 : checkPrefixCuts (2^48) 7807696897 10 Manual.Count131072.C059538.packed 64 cuts59538 = true := by
 decide +kernel
def cuts59539 : List PrefixCut := [⟨23,74443742,74443784⟩,
⟨64,207035389,207035503⟩]
theorem checked59539 : checkPrefixCuts (2^48) 7807827969 10 Manual.Count131072.C059539.packed 64 cuts59539 = true := by
 decide +kernel
def pointBounds59539 : List (Nat × Nat × Nat) := [(7807875072,113821595650665,113821984003576)]
theorem point_links_checked59539 : (cuts59539.take 1).map (fun c => (7807827969-1+2*2^10*c.k,113821521206923+c.lower,113821909559792+c.upper)) = pointBounds59539 := by
 decide +kernel
def cuts59540 : List PrefixCut := [⟨64,205373636,205373757⟩]
theorem checked59540 : checkPrefixCuts (2^48) 7807959041 10 Manual.Count131072.C059540.packed 64 cuts59540 = true := by
 decide +kernel
def cuts59541 : List PrefixCut := [⟨15,47440571,47440598⟩,
⟨64,207352891,207353009⟩]
theorem checked59541 : checkPrefixCuts (2^48) 7808090113 10 Manual.Count131072.C059541.packed 64 cuts59541 = true := by
 decide +kernel
def pointBounds59541 : List (Nat × Nat × Nat) := [(7808120832,113821981056519,113822369409650)]
theorem point_links_checked59541 : (cuts59541.take 1).map (fun c => (7808090113-1+2*2^10*c.k,113821933615948+c.lower,113822321969052+c.upper)) = pointBounds59541 := by
 decide +kernel
def cuts59542 : List PrefixCut := [⟨64,208575047,208575168⟩]
theorem checked59542 : checkPrefixCuts (2^48) 7808221185 10 Manual.Count131072.C059542.packed 64 cuts59542 = true := by
 decide +kernel
def cuts59543 : List PrefixCut := [⟨7,23827655,23827669⟩,
⟨64,208138976,208139094⟩]
theorem checked59543 : checkPrefixCuts (2^48) 7808352257 10 Manual.Count131072.C059543.packed 64 cuts59543 = true := by
 decide +kernel
def pointBounds59543 : List (Nat × Nat × Nat) := [(7808366592,113822373371541,113822761724898)]
theorem point_links_checked59543 : (cuts59543.take 1).map (fun c => (7808352257-1+2*2^10*c.k,113822349543886+c.lower,113822737897229+c.upper)) = pointBounds59543 := by
 decide +kernel
def cuts59544 : List PrefixCut := [⟨63,204602897,204603016⟩,
⟨64,207450588,207450709⟩]
theorem checked59544 : checkPrefixCuts (2^48) 7808483329 10 Manual.Count131072.C059544.packed 64 cuts59544 = true := by
 decide +kernel
def pointBounds59544 : List (Nat × Nat × Nat) := [(7808612352,113822762285759,113823150639339)]
theorem point_links_checked59544 : (cuts59544.take 1).map (fun c => (7808483329-1+2*2^10*c.k,113822557682862+c.lower,113822946036323+c.upper)) = pointBounds59544 := by
 decide +kernel
def cuts59545 : List PrefixCut := [⟨64,210511046,210511167⟩]
theorem checked59545 : checkPrefixCuts (2^48) 7808614401 10 Manual.Count131072.C059545.packed 64 cuts59545 = true := by
 decide +kernel
def cuts59546 : List PrefixCut := [⟨55,179544367,179544468⟩,
⟨64,207407576,207407693⟩]
theorem checked59546 : checkPrefixCuts (2^48) 7808745473 10 Manual.Count131072.C059546.packed 64 cuts59546 = true := by
 decide +kernel
def pointBounds59546 : List (Nat × Nat × Nat) := [(7808858112,113823155188863,113823543542667)]
theorem point_links_checked59546 : (cuts59546.take 1).map (fun c => (7808745473-1+2*2^10*c.k,113822975644496+c.lower,113823363998199+c.upper)) = pointBounds59546 := by
 decide +kernel
def cuts59547 : List PrefixCut := [⟨64,207043642,207043756⟩]
theorem checked59547 : checkPrefixCuts (2^48) 7808876545 10 Manual.Count131072.C059547.packed 64 cuts59547 = true := by
 decide +kernel
def cuts59548 : List PrefixCut := [⟨47,150774885,150774970⟩,
⟨64,206283224,206283341⟩]
theorem checked59548 : checkPrefixCuts (2^48) 7809007617 10 Manual.Count131072.C059548.packed 64 cuts59548 = true := by
 decide +kernel
def pointBounds59548 : List (Nat × Nat × Nat) := [(7809103872,113823540870599,113823929224618)]
theorem point_links_checked59548 : (cuts59548.take 1).map (fun c => (7809007617-1+2*2^10*c.k,113823390095714+c.lower,113823778449648+c.upper)) = pointBounds59548 := by
 decide +kernel
def cuts59549 : List PrefixCut := [⟨64,205883285,205883403⟩]
theorem checked59549 : checkPrefixCuts (2^48) 7809138689 10 Manual.Count131072.C059549.packed 64 cuts59549 = true := by
 decide +kernel
def cuts59550 : List PrefixCut := [⟨39,126765003,126765077⟩,
⟨64,207429691,207429812⟩]
theorem checked59550 : checkPrefixCuts (2^48) 7809269761 10 Manual.Count131072.C059550.packed 64 cuts59550 = true := by
 decide +kernel
def pointBounds59550 : List (Nat × Nat × Nat) := [(7809349632,113823929027226,113824317381469)]
theorem point_links_checked59550 : (cuts59550.take 1).map (fun c => (7809269761-1+2*2^10*c.k,113823802262223+c.lower,113824190616392+c.upper)) = pointBounds59550 := by
 decide +kernel
def cuts59551 : List PrefixCut := [⟨64,204939274,204939391⟩]
theorem checked59551 : checkPrefixCuts (2^48) 7809400833 10 Manual.Count131072.C059551.packed 64 cuts59551 = true := by
 decide +kernel
def cuts59552 : List PrefixCut := [⟨31,101675427,101675486⟩,
⟨64,211747784,211747904⟩]
theorem checked59552 : checkPrefixCuts (2^48) 7809531905 10 Manual.Count131072.C059552.packed 64 cuts59552 = true := by
 decide +kernel
def pointBounds59552 : List (Nat × Nat × Nat) := [(7809595392,113824316306615,113824704661081)]
theorem point_links_checked59552 : (cuts59552.take 1).map (fun c => (7809531905-1+2*2^10*c.k,113824214631188+c.lower,113824602985595+c.upper)) = pointBounds59552 := by
 decide +kernel
def cuts59553 : List PrefixCut := [⟨64,207887793,207887915⟩]
theorem checked59553 : checkPrefixCuts (2^48) 7809662977 10 Manual.Count131072.C059553.packed 64 cuts59553 = true := by
 decide +kernel
def cuts59554 : List PrefixCut := [⟨23,72767102,72767147⟩,
⟨64,206514730,206514851⟩]
theorem checked59554 : checkPrefixCuts (2^48) 7809794049 10 Manual.Count131072.C059554.packed 64 cuts59554 = true := by
 decide +kernel
def pointBounds59554 : List (Nat × Nat × Nat) := [(7809841152,113824707033867,113825095388561)]
theorem point_links_checked59554 : (cuts59554.take 1).map (fun c => (7809794049-1+2*2^10*c.k,113824634266765+c.lower,113825022621414+c.upper)) = pointBounds59554 := by
 decide +kernel
def cuts59555 : List PrefixCut := [⟨64,209142232,209142351⟩]
theorem checked59555 : checkPrefixCuts (2^48) 7809925121 10 Manual.Count131072.C059555.packed 64 cuts59555 = true := by
 decide +kernel
def cuts59556 : List PrefixCut := [⟨15,47933185,47933213⟩,
⟨64,205498692,205498812⟩]
theorem checked59556 : checkPrefixCuts (2^48) 7810056193 10 Manual.Count131072.C059556.packed 64 cuts59556 = true := by
 decide +kernel
def pointBounds59556 : List (Nat × Nat × Nat) := [(7810086912,113825097856912,113825486211829)]
theorem point_links_checked59556 : (cuts59556.take 1).map (fun c => (7810056193-1+2*2^10*c.k,113825049923727+c.lower,113825438278616+c.upper)) = pointBounds59556 := by
 decide +kernel
def cuts59557 : List PrefixCut := [⟨64,205927719,205927836⟩]
theorem checked59557 : checkPrefixCuts (2^48) 7810187265 10 Manual.Count131072.C059557.packed 64 cuts59557 = true := by
 decide +kernel
def cuts59558 : List PrefixCut := [⟨7,22091795,22091807⟩,
⟨64,207978452,207978569⟩]
theorem checked59558 : checkPrefixCuts (2^48) 7810318337 10 Manual.Count131072.C059558.packed 64 cuts59558 = true := by
 decide +kernel
def pointBounds59558 : List (Nat × Nat × Nat) := [(7810332672,113825483441933,113825871797071)]
theorem point_links_checked59558 : (cuts59558.take 1).map (fun c => (7810318337-1+2*2^10*c.k,113825461350138+c.lower,113825849705264+c.upper)) = pointBounds59558 := by
 decide +kernel
def cuts59559 : List PrefixCut := [⟨63,202857599,202857711⟩,
⟨64,205812686,205812800⟩]
theorem checked59559 : checkPrefixCuts (2^48) 7810449409 10 Manual.Count131072.C059559.packed 64 cuts59559 = true := by
 decide +kernel
def pointBounds59559 : List (Nat × Nat × Nat) := [(7810578432,113825872186189,113826260541544)]
theorem point_links_checked59559 : (cuts59559.take 1).map (fun c => (7810449409-1+2*2^10*c.k,113825669328590+c.lower,113826057683833+c.upper)) = pointBounds59559 := by
 decide +kernel
def cuts59560 : List PrefixCut := [⟨64,207647138,207647256⟩]
theorem checked59560 : checkPrefixCuts (2^48) 7810580481 10 Manual.Count131072.C059560.packed 64 cuts59560 = true := by
 decide +kernel
def cuts59561 : List PrefixCut := [⟨55,181301021,181301121⟩,
⟨64,209625689,209625806⟩]
theorem checked59561 : checkPrefixCuts (2^48) 7810711553 10 Manual.Count131072.C059561.packed 64 cuts59561 = true := by
 decide +kernel
def pointBounds59561 : List (Nat × Nat × Nat) := [(7810824192,113826264089435,113826652445010)]
theorem point_links_checked59561 : (cuts59561.take 1).map (fun c => (7810711553-1+2*2^10*c.k,113826082788414+c.lower,113826471143889+c.upper)) = pointBounds59561 := by
 decide +kernel
def cuts59562 : List PrefixCut := [⟨64,204180705,204180821⟩]
theorem checked59562 : checkPrefixCuts (2^48) 7810842625 10 Manual.Count131072.C059562.packed 64 cuts59562 = true := by
 decide +kernel
def cuts59563 : List PrefixCut := [⟨47,150124334,150124416⟩,
⟨64,206087158,206087271⟩]
theorem checked59563 : checkPrefixCuts (2^48) 7810973697 10 Manual.Count131072.C059563.packed 64 cuts59563 = true := by
 decide +kernel
def pointBounds59563 : List (Nat × Nat × Nat) := [(7811069952,113826646719142,113827035074932)]
theorem point_links_checked59563 : (cuts59563.take 1).map (fun c => (7810973697-1+2*2^10*c.k,113826496594808+c.lower,113826884950516+c.upper)) = pointBounds59563 := by
 decide +kernel
def cuts59564 : List PrefixCut := [⟨64,211993433,211993551⟩]
theorem checked59564 : checkPrefixCuts (2^48) 7811104769 10 Manual.Count131072.C059564.packed 64 cuts59564 = true := by
 decide +kernel
def cuts59565 : List PrefixCut := [⟨39,125580004,125580078⟩,
⟨64,206296455,206296574⟩]
theorem checked59565 : checkPrefixCuts (2^48) 7811235841 10 Manual.Count131072.C059565.packed 64 cuts59565 = true := by
 decide +kernel
def pointBounds59565 : List (Nat × Nat × Nat) := [(7811315712,113827040255403,113827428611416)]
theorem point_links_checked59565 : (cuts59565.take 1).map (fun c => (7811235841-1+2*2^10*c.k,113826914675399+c.lower,113827303031338+c.upper)) = pointBounds59565 := by
 decide +kernel
def cuts59566 : List PrefixCut := [⟨64,205752493,205752612⟩]
theorem checked59566 : checkPrefixCuts (2^48) 7811366913 10 Manual.Count131072.C059566.packed 64 cuts59566 = true := by
 decide +kernel
def cuts59567 : List PrefixCut := [⟨31,99559905,99559962⟩,
⟨64,207334486,207334607⟩]
theorem checked59567 : checkPrefixCuts (2^48) 7811497985 10 Manual.Count131072.C059567.packed 64 cuts59567 = true := by
 decide +kernel
def pointBounds59567 : List (Nat × Nat × Nat) := [(7811561472,113827426284252,113827814640486)]
theorem point_links_checked59567 : (cuts59567.take 1).map (fun c => (7811497985-1+2*2^10*c.k,113827326724347+c.lower,113827715080524+c.upper)) = pointBounds59567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000298
