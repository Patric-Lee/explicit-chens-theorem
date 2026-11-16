import PlattAssemblyKernel
import PlattCertificates.Count131072.C027488
import PlattCertificates.Count131072.C027489
import PlattCertificates.Count131072.C027490
import PlattCertificates.Count131072.C027491
import PlattCertificates.Count131072.C027492
import PlattCertificates.Count131072.C027493
import PlattCertificates.Count131072.C027494
import PlattCertificates.Count131072.C027495
import PlattCertificates.Count131072.C027496
import PlattCertificates.Count131072.C027497
import PlattCertificates.Count131072.C027498
import PlattCertificates.Count131072.C027499
import PlattCertificates.Count131072.C027500
import PlattCertificates.Count131072.C027501
import PlattCertificates.Count131072.C027502
import PlattCertificates.Count131072.C027503
import PlattCertificates.Count131072.C027504
import PlattCertificates.Count131072.C027505
import PlattCertificates.Count131072.C027506
import PlattCertificates.Count131072.C027507
import PlattCertificates.Count131072.C027508
import PlattCertificates.Count131072.C027509
import PlattCertificates.Count131072.C027510
import PlattCertificates.Count131072.C027511
import PlattCertificates.Count131072.C027512
import PlattCertificates.Count131072.C027513
import PlattCertificates.Count131072.C027514
import PlattCertificates.Count131072.C027515
import PlattCertificates.Count131072.C027516
import PlattCertificates.Count131072.C027517
import PlattCertificates.Count131072.C027518
import PlattCertificates.Count131072.C027519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000234
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27488 : List PrefixCut := [⟨40,146868967,146869050⟩,
⟨128,464246842,464247101⟩]
theorem checked27488 : checkPrefixCuts (2^48) 3606839297 9 Manual.Count131072.C027488.packed 128 cuts27488 = true := by
 decide +kernel
def pointBounds27488 : List (Nat × Nat × Nat) := [(3606880256,104112959908252,104113342604933)]
theorem point_links_checked27488 : (cuts27488.take 1).map (fun c => (3606839297-1+2*2^9*c.k,104112813039285+c.lower,104113195735883+c.upper)) = pointBounds27488 := by
 decide +kernel
def cuts27489 : List PrefixCut := [⟨23,81313634,81313682⟩,
⟨128,463995837,463996103⟩]
theorem checked27489 : checkPrefixCuts (2^48) 3606970369 9 Manual.Count131072.C027489.packed 128 cuts27489 = true := by
 decide +kernel
def pointBounds27489 : List (Nat × Nat × Nat) := [(3606993920,104113358599761,104113741296666)]
theorem point_links_checked27489 : (cuts27489.take 1).map (fun c => (3606970369-1+2*2^9*c.k,104113277286127+c.lower,104113659982984+c.upper)) = pointBounds27489 := by
 decide +kernel
def cuts27490 : List PrefixCut := [⟨6,21147071,21147083⟩,
⟨117,421764284,421764521⟩,
⟨128,462184253,462184513⟩]
theorem checked27490 : checkPrefixCuts (2^48) 3607101441 9 Manual.Count131072.C027490.packed 128 cuts27490 = true := by
 decide +kernel
def pointBounds27490 : List (Nat × Nat × Nat) := [(3607107584,104113762429035,104114145126170),(3607221248,104114163046248,104114545743608)]
theorem point_links_checked27490 : (cuts27490.take 2).map (fun c => (3607101441-1+2*2^9*c.k,104113741281964+c.lower,104114123979087+c.upper)) = pointBounds27490 := by
 decide +kernel
def cuts27491 : List PrefixCut := [⟨100,356829352,356829555⟩,
⟨128,455925137,455925396⟩]
theorem checked27491 : checkPrefixCuts (2^48) 3607232513 9 Manual.Count131072.C027491.packed 128 cuts27491 = true := by
 decide +kernel
def pointBounds27491 : List (Nat × Nat × Nat) := [(3607334912,104114560295569,104114942993155)]
theorem point_links_checked27491 : (cuts27491.take 1).map (fun c => (3607232513-1+2*2^9*c.k,104114203466217+c.lower,104114586163600+c.upper)) = pointBounds27491 := by
 decide +kernel
def cuts27492 : List PrefixCut := [⟨83,301730278,301730445⟩,
⟨128,460200136,460200391⟩]
theorem checked27492 : checkPrefixCuts (2^48) 3607363585 9 Manual.Count131072.C027492.packed 128 cuts27492 = true := by
 decide +kernel
def pointBounds27492 : List (Nat × Nat × Nat) := [(3607448576,104114961121632,104115343819441)]
theorem point_links_checked27492 : (cuts27492.take 1).map (fun c => (3607363585-1+2*2^9*c.k,104114659391354+c.lower,104115042088996+c.upper)) = pointBounds27492 := by
 decide +kernel
def cuts27493 : List PrefixCut := [⟨66,241797336,241797474⟩,
⟨128,467049417,467049682⟩]
theorem checked27493 : checkPrefixCuts (2^48) 3607494657 9 Manual.Count131072.C027493.packed 128 cuts27493 = true := by
 decide +kernel
def pointBounds27493 : List (Nat × Nat × Nat) := [(3607562240,104115361388826,104115744086861)]
theorem point_links_checked27493 : (cuts27493.take 1).map (fun c => (3607494657-1+2*2^9*c.k,104115119591490+c.lower,104115502289387+c.upper)) = pointBounds27493 := by
 decide +kernel
def cuts27494 : List PrefixCut := [⟨49,177187179,177187280⟩,
⟨128,465628028,465628292⟩]
theorem checked27494 : checkPrefixCuts (2^48) 3607625729 9 Manual.Count131072.C027494.packed 128 cuts27494 = true := by
 decide +kernel
def pointBounds27494 : List (Nat × Nat × Nat) := [(3607675904,104115763828086,104116146526349)]
theorem point_links_checked27494 : (cuts27494.take 1).map (fun c => (3607625729-1+2*2^9*c.k,104115586640907+c.lower,104115969339069+c.upper)) = pointBounds27494 := by
 decide +kernel
def cuts27495 : List PrefixCut := [⟨32,115546159,115546225⟩,
⟨128,462490401,462490659⟩]
theorem checked27495 : checkPrefixCuts (2^48) 3607756801 9 Manual.Count131072.C027495.packed 128 cuts27495 = true := by
 decide +kernel
def pointBounds27495 : List (Nat × Nat × Nat) := [(3607789568,104116167815094,104116550513586)]
theorem point_links_checked27495 : (cuts27495.take 1).map (fun c => (3607756801-1+2*2^9*c.k,104116052268935+c.lower,104116434967361+c.upper)) = pointBounds27495 := by
 decide +kernel
def cuts27496 : List PrefixCut := [⟨15,55313606,55313635⟩,
⟨126,460991471,460991730⟩,
⟨128,468324761,468325024⟩]
theorem checked27496 : checkPrefixCuts (2^48) 3607887873 9 Manual.Count131072.C027496.packed 128 cuts27496 = true := by
 decide +kernel
def pointBounds27496 : List (Nat × Nat × Nat) := [(3607903232,104116570072942,104116952771655),(3608016896,104116975750807,104117358449750)]
theorem point_links_checked27496 : (cuts27496.take 2).map (fun c => (3607887873-1+2*2^9*c.k,104116514759336+c.lower,104116897458020+c.upper)) = pointBounds27496 := by
 decide +kernel
def cuts27497 : List PrefixCut := [⟨109,388970266,388970485⟩,
⟨128,457854040,457854297⟩]
theorem checked27497 : checkPrefixCuts (2^48) 3608018945 9 Manual.Count131072.C027497.packed 128 cuts27497 = true := by
 decide +kernel
def pointBounds27497 : List (Nat × Nat × Nat) := [(3608130560,104117372054363,104117754753529)]
theorem point_links_checked27497 : (cuts27497.take 1).map (fun c => (3608018945-1+2*2^9*c.k,104116983084097+c.lower,104117365783044+c.upper)) = pointBounds27497 := by
 decide +kernel
def cuts27498 : List PrefixCut := [⟨92,338016629,338016820⟩,
⟨128,470240910,470241172⟩]
theorem checked27498 : checkPrefixCuts (2^48) 3608150017 9 Manual.Count131072.C027498.packed 128 cuts27498 = true := by
 decide +kernel
def pointBounds27498 : List (Nat × Nat × Nat) := [(3608244224,104117778954766,104118161654161)]
theorem point_links_checked27498 : (cuts27498.take 1).map (fun c => (3608150017-1+2*2^9*c.k,104117440938137+c.lower,104117823637341+c.upper)) = pointBounds27498 := by
 decide +kernel
def cuts27499 : List PrefixCut := [⟨75,273649242,273649397⟩,
⟨128,466323513,466323774⟩]
theorem checked27499 : checkPrefixCuts (2^48) 3608281089 9 Manual.Count131072.C027499.packed 128 cuts27499 = true := by
 decide +kernel
def pointBounds27499 : List (Nat × Nat × Nat) := [(3608357888,104118184828289,104118567527910)]
theorem point_links_checked27499 : (cuts27499.take 1).map (fun c => (3608281089-1+2*2^9*c.k,104117911179047+c.lower,104118293878513+c.upper)) = pointBounds27499 := by
 decide +kernel
def cuts27500 : List PrefixCut := [⟨58,208740178,208740295⟩,
⟨128,463342429,463342691⟩]
theorem checked27500 : checkPrefixCuts (2^48) 3608412161 9 Manual.Count131072.C027500.packed 128 cuts27500 = true := by
 decide +kernel
def pointBounds27500 : List (Nat × Nat × Nat) := [(3608471552,104118586242738,104118968942582)]
theorem point_links_checked27500 : (cuts27500.take 1).map (fun c => (3608412161-1+2*2^9*c.k,104118377502560+c.lower,104118760202287+c.upper)) = pointBounds27500 := by
 decide +kernel
def cuts27501 : List PrefixCut := [⟨41,147033594,147033677⟩,
⟨128,466913590,466913850⟩]
theorem checked27501 : checkPrefixCuts (2^48) 3608543233 9 Manual.Count131072.C027501.packed 128 cuts27501 = true := by
 decide +kernel
def pointBounds27501 : List (Nat × Nat × Nat) := [(3608585216,104118987878583,104119370578655)]
theorem point_links_checked27501 : (cuts27501.take 1).map (fun c => (3608543233-1+2*2^9*c.k,104118840844989+c.lower,104119223544978+c.upper)) = pointBounds27501 := by
 decide +kernel
def cuts27502 : List PrefixCut := [⟨24,84785193,84785240⟩,
⟨128,461592848,461593103⟩]
theorem checked27502 : checkPrefixCuts (2^48) 3608674305 9 Manual.Count131072.C027502.packed 128 cuts27502 = true := by
 decide +kernel
def pointBounds27502 : List (Nat × Nat × Nat) := [(3608698880,104119392543772,104119775244068)]
theorem point_links_checked27502 : (cuts27502.take 1).map (fun c => (3608674305-1+2*2^9*c.k,104119307758579+c.lower,104119690458828+c.upper)) = pointBounds27502 := by
 decide +kernel
def cuts27503 : List PrefixCut := [⟨7,24802924,24802938⟩,
⟨118,430534558,430534804⟩,
⟨128,466489781,466490046⟩]
theorem checked27503 : checkPrefixCuts (2^48) 3608805377 9 Manual.Count131072.C027503.packed 128 cuts27503 = true := by
 decide +kernel
def pointBounds27503 : List (Nat × Nat × Nat) := [(3608812544,104119794154351,104120176854869),(3608926208,104120199885985,104120582586735)]
theorem point_links_checked27503 : (cuts27503.take 2).map (fun c => (3608805377-1+2*2^9*c.k,104119769351427+c.lower,104120152051931+c.upper)) = pointBounds27503 := by
 decide +kernel
def cuts27504 : List PrefixCut := [⟨101,369841598,369841802⟩,
⟨128,471854257,471854514⟩]
theorem checked27504 : checkPrefixCuts (2^48) 3608936449 9 Manual.Count131072.C027504.packed 128 cuts27504 = true := by
 decide +kernel
def pointBounds27504 : List (Nat × Nat × Nat) := [(3609039872,104120605682806,104120988383779)]
theorem point_links_checked27504 : (cuts27504.take 1).map (fun c => (3608936449-1+2*2^9*c.k,104120235841208+c.lower,104120618541977+c.upper)) = pointBounds27504 := by
 decide +kernel
def cuts27505 : List PrefixCut := [⟨84,301587758,301587931⟩,
⟨128,456941217,456941482⟩]
theorem checked27505 : checkPrefixCuts (2^48) 3609067521 9 Manual.Count131072.C027505.packed 128 cuts27505 = true := by
 decide +kernel
def pointBounds27505 : List (Nat × Nat × Nat) := [(3609153536,104121009283223,104121391984422)]
theorem point_links_checked27505 : (cuts27505.take 1).map (fun c => (3609067521-1+2*2^9*c.k,104120707695465+c.lower,104121090396491+c.upper)) = pointBounds27505 := by
 decide +kernel
def cuts27506 : List PrefixCut := [⟨67,241761093,241761224⟩,
⟨128,465269101,465269354⟩]
theorem checked27506 : checkPrefixCuts (2^48) 3609198593 9 Manual.Count131072.C027506.packed 128 cuts27506 = true := by
 decide +kernel
def pointBounds27506 : List (Nat × Nat × Nat) := [(3609267200,104121406397775,104121789099197)]
theorem point_links_checked27506 : (cuts27506.take 1).map (fun c => (3609198593-1+2*2^9*c.k,104121164636682+c.lower,104121547337973+c.upper)) = pointBounds27506 := by
 decide +kernel
def cuts27507 : List PrefixCut := [⟨50,183888180,183888283⟩,
⟨128,465174294,465174557⟩]
theorem checked27507 : checkPrefixCuts (2^48) 3609329665 9 Manual.Count131072.C027507.packed 128 cuts27507 = true := by
 decide +kernel
def pointBounds27507 : List (Nat × Nat × Nat) := [(3609380864,104121813793963,104122196495610)]
theorem point_links_checked27507 : (cuts27507.take 1).map (fun c => (3609329665-1+2*2^9*c.k,104121629905783+c.lower,104122012607327+c.upper)) = pointBounds27507 := by
 decide +kernel
def cuts27508 : List PrefixCut := [⟨33,126175150,126175219⟩,
⟨128,467418934,467419195⟩]
theorem checked27508 : checkPrefixCuts (2^48) 3609460737 9 Manual.Count131072.C027508.packed 128 cuts27508 = true := by
 decide +kernel
def pointBounds27508 : List (Nat × Nat × Nat) := [(3609494528,104122221255227,104122603957103)]
theorem point_links_checked27508 : (cuts27508.take 1).map (fun c => (3609460737-1+2*2^9*c.k,104122095080077+c.lower,104122477781884+c.upper)) = pointBounds27508 := by
 decide +kernel
def cuts27509 : List PrefixCut := [⟨16,57626866,57626899⟩,
⟨127,460773715,460773974⟩,
⟨128,464984467,464984728⟩]
theorem checked27509 : checkPrefixCuts (2^48) 3609591809 9 Manual.Count131072.C027509.packed 128 cuts27509 = true := by
 decide +kernel
def pointBounds27509 : List (Nat × Nat × Nat) := [(3609608192,104122620125877,104123002827978),(3609721856,104123023272726,104123405975053)]
theorem point_links_checked27509 : (cuts27509.take 2).map (fun c => (3609591809-1+2*2^9*c.k,104122562499011+c.lower,104122945201079+c.upper)) = pointBounds27509 := by
 decide +kernel
def cuts27510 : List PrefixCut := [⟨110,393933054,393933277⟩,
⟨128,460445077,460445335⟩]
theorem checked27510 : checkPrefixCuts (2^48) 3609722881 9 Manual.Count131072.C027510.packed 128 cuts27510 = true := by
 decide +kernel
def pointBounds27510 : List (Nat × Nat × Nat) := [(3609835520,104123421416532,104123804119084)]
theorem point_links_checked27510 : (cuts27510.take 1).map (fun c => (3609722881-1+2*2^9*c.k,104123027483478+c.lower,104123410185807+c.upper)) = pointBounds27510 := by
 decide +kernel
def cuts27511 : List PrefixCut := [⟨93,330215677,330215865⟩,
⟨128,455204147,455204406⟩]
theorem checked27511 : checkPrefixCuts (2^48) 3609853953 9 Manual.Count131072.C027511.packed 128 cuts27511 = true := by
 decide +kernel
def pointBounds27511 : List (Nat × Nat × Nat) := [(3609949184,104123818144232,104124200847007)]
theorem point_links_checked27511 : (cuts27511.take 1).map (fun c => (3609853953-1+2*2^9*c.k,104123487928555+c.lower,104123870631142+c.upper)) = pointBounds27511 := by
 decide +kernel
def cuts27512 : List PrefixCut := [⟨76,278198257,278198407⟩,
⟨128,466025459,466025716⟩]
theorem checked27512 : checkPrefixCuts (2^48) 3609985025 9 Manual.Count131072.C027512.packed 128 cuts27512 = true := by
 decide +kernel
def pointBounds27512 : List (Nat × Nat × Nat) := [(3610062848,104124221330959,104124604033955)]
theorem point_links_checked27512 : (cuts27512.take 1).map (fun c => (3609985025-1+2*2^9*c.k,104123943132702+c.lower,104124325835548+c.upper)) = pointBounds27512 := by
 decide +kernel
def cuts27513 : List PrefixCut := [⟨59,214411257,214411377⟩,
⟨128,462655951,462656211⟩]
theorem checked27513 : checkPrefixCuts (2^48) 3610116097 9 Manual.Count131072.C027513.packed 128 cuts27513 = true := by
 decide +kernel
def pointBounds27513 : List (Nat × Nat × Nat) := [(3610176512,104124623569418,104125006272641)]
theorem point_links_checked27513 : (cuts27513.take 1).map (fun c => (3610116097-1+2*2^9*c.k,104124409158161+c.lower,104124791861264+c.upper)) = pointBounds27513 := by
 decide +kernel
def cuts27514 : List PrefixCut := [⟨42,150472606,150472692⟩,
⟨128,459286699,459286960⟩]
theorem checked27514 : checkPrefixCuts (2^48) 3610247169 9 Manual.Count131072.C027514.packed 128 cuts27514 = true := by
 decide +kernel
def pointBounds27514 : List (Nat × Nat × Nat) := [(3610290176,104125022286718,104125404990167)]
theorem point_links_checked27514 : (cuts27514.take 1).map (fun c => (3610247169-1+2*2^9*c.k,104124871814112+c.lower,104125254517475+c.upper)) = pointBounds27514 := by
 decide +kernel
def cuts27515 : List PrefixCut := [⟨25,89890690,89890742⟩,
⟨128,465273048,465273307⟩]
theorem checked27515 : checkPrefixCuts (2^48) 3610378241 9 Manual.Count131072.C027515.packed 128 cuts27515 = true := by
 decide +kernel
def pointBounds27515 : List (Nat × Nat × Nat) := [(3610403840,104125420991501,104125803695177)]
theorem point_links_checked27515 : (cuts27515.take 1).map (fun c => (3610378241-1+2*2^9*c.k,104125331100811+c.lower,104125713804435+c.upper)) = pointBounds27515 := by
 decide +kernel
def cuts27516 : List PrefixCut := [⟨8,28377366,28377382⟩,
⟨119,428304369,428304610⟩,
⟨128,461903904,461904164⟩]
theorem checked27516 : checkPrefixCuts (2^48) 3610509313 9 Manual.Count131072.C027516.packed 128 cuts27516 = true := by
 decide +kernel
def pointBounds27516 : List (Nat × Nat × Nat) := [(3610517504,104125824751225,104126207455124),(3610631168,104126224678228,104126607382352)]
theorem point_links_checked27516 : (cuts27516.take 2).map (fun c => (3610509313-1+2*2^9*c.k,104125796373859+c.lower,104126179077742+c.upper)) = pointBounds27516 := by
 decide +kernel
def cuts27517 : List PrefixCut := [⟨102,366626742,366626949⟩,
⟨128,460561931,460562192⟩]
theorem checked27517 : checkPrefixCuts (2^48) 3610640385 9 Manual.Count131072.C027517.packed 128 cuts27517 = true := by
 decide +kernel
def pointBounds27517 : List (Nat × Nat × Nat) := [(3610744832,104126624904505,104127007608855)]
theorem point_links_checked27517 : (cuts27517.take 1).map (fun c => (3610640385-1+2*2^9*c.k,104126258277763+c.lower,104126640981906+c.upper)) = pointBounds27517 := by
 decide +kernel
def cuts27518 : List PrefixCut := [⟨85,307759570,307759743⟩,
⟨128,463585347,463585610⟩]
theorem checked27518 : checkPrefixCuts (2^48) 3610771457 9 Manual.Count131072.C027518.packed 128 cuts27518 = true := by
 decide +kernel
def pointBounds27518 : List (Nat × Nat × Nat) := [(3610858496,104127026599264,104127409303841)]
theorem point_links_checked27518 : (cuts27518.take 1).map (fun c => (3610771457-1+2*2^9*c.k,104126718839694+c.lower,104127101544098+c.upper)) = pointBounds27518 := by
 decide +kernel
def cuts27519 : List PrefixCut := [⟨68,248350770,248350909⟩,
⟨128,466842468,466842730⟩]
theorem checked27519 : checkPrefixCuts (2^48) 3610902529 9 Manual.Count131072.C027519.packed 128 cuts27519 = true := by
 decide +kernel
def pointBounds27519 : List (Nat × Nat × Nat) := [(3610972160,104127430775811,104127813480617)]
theorem point_links_checked27519 : (cuts27519.take 1).map (fun c => (3610902529-1+2*2^9*c.k,104127182425041+c.lower,104127565129708+c.upper)) = pointBounds27519 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000234
