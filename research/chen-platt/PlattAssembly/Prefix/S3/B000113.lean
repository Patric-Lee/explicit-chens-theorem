import PlattAssemblyKernel
import PlattCertificates.Count131072.C023616
import PlattCertificates.Count131072.C023617
import PlattCertificates.Count131072.C023618
import PlattCertificates.Count131072.C023619
import PlattCertificates.Count131072.C023620
import PlattCertificates.Count131072.C023621
import PlattCertificates.Count131072.C023622
import PlattCertificates.Count131072.C023623
import PlattCertificates.Count131072.C023624
import PlattCertificates.Count131072.C023625
import PlattCertificates.Count131072.C023626
import PlattCertificates.Count131072.C023627
import PlattCertificates.Count131072.C023628
import PlattCertificates.Count131072.C023629
import PlattCertificates.Count131072.C023630
import PlattCertificates.Count131072.C023631
import PlattCertificates.Count131072.C023632
import PlattCertificates.Count131072.C023633
import PlattCertificates.Count131072.C023634
import PlattCertificates.Count131072.C023635
import PlattCertificates.Count131072.C023636
import PlattCertificates.Count131072.C023637
import PlattCertificates.Count131072.C023638
import PlattCertificates.Count131072.C023639
import PlattCertificates.Count131072.C023640
import PlattCertificates.Count131072.C023641
import PlattCertificates.Count131072.C023642
import PlattCertificates.Count131072.C023643
import PlattCertificates.Count131072.C023644
import PlattCertificates.Count131072.C023645
import PlattCertificates.Count131072.C023646
import PlattCertificates.Count131072.C023647
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000113
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23616 : List PrefixCut := [⟨75,326850027,326850212⟩,
⟨128,555158890,555159210⟩]
theorem checked23616 : checkPrefixCuts (2^48) 3099328513 9 Manual.Count131072.C023616.packed 128 cuts23616 = true := by
 decide +kernel
def pointBounds23616 : List (Nat × Nat × Nat) := [(3099405312,102166740049836,102167121654184)]
theorem point_links_checked23616 : (cuts23616.take 1).map (fun c => (3099328513-1+2*2^9*c.k,102166413199809+c.lower,102166794803972+c.upper)) = pointBounds23616 := by
 decide +kernel
def cuts23617 : List PrefixCut := [⟨42,174362016,174362113⟩,
⟨128,539243134,539243439⟩]
theorem checked23617 : checkPrefixCuts (2^48) 3099459585 9 Manual.Count131072.C023617.packed 128 cuts23617 = true := by
 decide +kernel
def pointBounds23617 : List (Nat × Nat × Nat) := [(3099502592,102167142720715,102167524325295)]
theorem point_links_checked23617 : (cuts23617.take 1).map (fun c => (3099459585-1+2*2^9*c.k,102166968358699+c.lower,102167349963182+c.upper)) = pointBounds23617 := by
 decide +kernel
def cuts23618 : List PrefixCut := [⟨9,39048391,39048413⟩,
⟨104,446143582,446143833⟩,
⟨128,548755334,548755647⟩]
theorem checked23618 : checkPrefixCuts (2^48) 3099590657 9 Manual.Count131072.C023618.packed 128 cuts23618 = true := by
 decide +kernel
def pointBounds23618 : List (Nat × Nat × Nat) := [(3099599872,102167546650224,102167928255034),(3099697152,102167953745415,102168335350454)]
theorem point_links_checked23618 : (cuts23618.take 2).map (fun c => (3099590657-1+2*2^9*c.k,102167507601833+c.lower,102167889206621+c.upper)) = pointBounds23618 := by
 decide +kernel
def cuts23619 : List PrefixCut := [⟨71,301292450,301292619⟩,
⟨128,540378117,540378425⟩]
theorem checked23619 : checkPrefixCuts (2^48) 3099721729 9 Manual.Count131072.C023619.packed 128 cuts23619 = true := by
 decide +kernel
def pointBounds23619 : List (Nat × Nat × Nat) := [(3099794432,102168357649617,102168739254887)]
theorem point_links_checked23619 : (cuts23619.take 1).map (fun c => (3099721729-1+2*2^9*c.k,102168056357167+c.lower,102168437962268+c.upper)) = pointBounds23619 := by
 decide +kernel
def cuts23620 : List PrefixCut := [⟨38,163988575,163988669⟩,
⟨128,545621717,545622023⟩]
theorem checked23620 : checkPrefixCuts (2^48) 3099852801 9 Manual.Count131072.C023620.packed 128 cuts23620 = true := by
 decide +kernel
def pointBounds23620 : List (Nat × Nat × Nat) := [(3099891712,102168760723859,102169142329362)]
theorem point_links_checked23620 : (cuts23620.take 1).map (fun c => (3099852801-1+2*2^9*c.k,102168596735284+c.lower,102168978340693+c.upper)) = pointBounds23620 := by
 decide +kernel
def cuts23621 : List PrefixCut := [⟨5,19340135,19340145⟩,
⟨100,423932710,423932954⟩,
⟨128,540332431,540332739⟩]
theorem checked23621 : checkPrefixCuts (2^48) 3099983873 9 Manual.Count131072.C023621.packed 128 cuts23621 = true := by
 decide +kernel
def pointBounds23621 : List (Nat × Nat × Nat) := [(3099988992,102169161697136,102169543302861),(3100086272,102169566289711,102169947895670)]
theorem point_links_checked23621 : (cuts23621.take 2).map (fun c => (3099983873-1+2*2^9*c.k,102169142357001+c.lower,102169523962716+c.upper)) = pointBounds23621 := by
 decide +kernel
def cuts23622 : List PrefixCut := [⟨67,280371787,280371941⟩,
⟨128,539129122,539129419⟩]
theorem checked23622 : checkPrefixCuts (2^48) 3100114945 9 Manual.Count131072.C023622.packed 128 cuts23622 = true := by
 decide +kernel
def pointBounds23622 : List (Nat × Nat × Nat) := [(3100183552,102169963061219,102170344667396)]
theorem point_links_checked23622 : (cuts23622.take 1).map (fun c => (3100114945-1+2*2^9*c.k,102169682689432+c.lower,102170064295455+c.upper)) = pointBounds23622 := by
 decide +kernel
def cuts23623 : List PrefixCut := [⟨34,141361009,141361091⟩,
⟨128,539741930,539742231⟩]
theorem checked23623 : checkPrefixCuts (2^48) 3100246017 9 Manual.Count131072.C023623.packed 128 cuts23623 = true := by
 decide +kernel
def pointBounds23623 : List (Nat × Nat × Nat) := [(3100280832,102170363179563,102170744785965)]
theorem point_links_checked23623 : (cuts23623.take 1).map (fun c => (3100246017-1+2*2^9*c.k,102170221818554+c.lower,102170603424874+c.upper)) = pointBounds23623 := by
 decide +kernel
def cuts23624 : List PrefixCut := [⟨1,3994641,3994643⟩,
⟨96,405177358,405177587⟩,
⟨128,542987403,542987708⟩]
theorem checked23624 : checkPrefixCuts (2^48) 3100377089 9 Manual.Count131072.C023624.packed 128 cuts23624 = true := by
 decide +kernel
def pointBounds23624 : List (Nat × Nat × Nat) := [(3100378112,102170765555125,102171147161748),(3100475392,102171166737842,102171548344692)]
theorem point_links_checked23624 : (cuts23624.take 2).map (fun c => (3100377089-1+2*2^9*c.k,102170761560484+c.lower,102171143167105+c.upper)) = pointBounds23624 := by
 decide +kernel
def cuts23625 : List PrefixCut := [⟨63,262906194,262906344⟩,
⟨128,535883530,535883835⟩]
theorem checked23625 : checkPrefixCuts (2^48) 3100508161 9 Manual.Count131072.C023625.packed 128 cuts23625 = true := by
 decide +kernel
def pointBounds23625 : List (Nat × Nat × Nat) := [(3100572672,102171567454081,102171949061157)]
theorem point_links_checked23625 : (cuts23625.take 1).map (fun c => (3100508161-1+2*2^9*c.k,102171304547887+c.lower,102171686154813+c.upper)) = pointBounds23625 := by
 decide +kernel
def cuts23626 : List PrefixCut := [⟨30,127544751,127544826⟩,
⟨125,531594594,531594893⟩,
⟨128,544484764,544485069⟩]
theorem checked23626 : checkPrefixCuts (2^48) 3100639233 9 Manual.Count131072.C023626.packed 128 cuts23626 = true := by
 decide +kernel
def pointBounds23626 : List (Nat × Nat × Nat) := [(3100669952,102171967976168,102172349583474),(3100767232,102172372026011,102172753633541)]
theorem point_links_checked23626 : (cuts23626.take 2).map (fun c => (3100639233-1+2*2^9*c.k,102171840431417+c.lower,102172222038648+c.upper)) = pointBounds23626 := by
 decide +kernel
def cuts23627 : List PrefixCut := [⟨92,391146992,391147205⟩,
⟨128,544734081,544734384⟩]
theorem checked23627 : checkPrefixCuts (2^48) 3100770305 9 Manual.Count131072.C023627.packed 128 cuts23627 = true := by
 decide +kernel
def pointBounds23627 : List (Nat × Nat × Nat) := [(3100864512,102172776063173,102173157670922)]
theorem point_links_checked23627 : (cuts23627.take 1).map (fun c => (3100770305-1+2*2^9*c.k,102172384916181+c.lower,102172766523717+c.upper)) = pointBounds23627 := by
 decide +kernel
def cuts23628 : List PrefixCut := [⟨59,248985043,248985181⟩,
⟨128,542532462,542532767⟩]
theorem checked23628 : checkPrefixCuts (2^48) 3100901377 9 Manual.Count131072.C023628.packed 128 cuts23628 = true := by
 decide +kernel
def pointBounds23628 : List (Nat × Nat × Nat) := [(3100961792,102173178635305,102173560243282)]
theorem point_links_checked23628 : (cuts23628.take 1).map (fun c => (3100901377-1+2*2^9*c.k,102172929650262+c.lower,102173311258101+c.upper)) = pointBounds23628 := by
 decide +kernel
def cuts23629 : List PrefixCut := [⟨26,108013595,108013659⟩,
⟨121,514009500,514009801⟩,
⟨128,543235634,543235950⟩]
theorem checked23629 : checkPrefixCuts (2^48) 3101032449 9 Manual.Count131072.C023629.packed 128 cuts23629 = true := by
 decide +kernel
def pointBounds23629 : List (Nat × Nat × Nat) := [(3101059072,102173580196319,102173961804527),(3101156352,102173986192224,102174367800669)]
theorem point_links_checked23629 : (cuts23629.take 2).map (fun c => (3101032449-1+2*2^9*c.k,102173472182724+c.lower,102173853790868+c.upper)) = pointBounds23629 := by
 decide +kernel
def cuts23630 : List PrefixCut := [⟨88,368588363,368588579⟩,
⟨128,538946866,538947176⟩]
theorem checked23630 : checkPrefixCuts (2^48) 3101163521 9 Manual.Count131072.C023630.packed 128 cuts23630 = true := by
 decide +kernel
def pointBounds23630 : List (Nat × Nat × Nat) := [(3101253632,102174384006721,102174765615397)]
theorem point_links_checked23630 : (cuts23630.take 1).map (fun c => (3101163521-1+2*2^9*c.k,102174015418358+c.lower,102174397026818+c.upper)) = pointBounds23630 := by
 decide +kernel
def cuts23631 : List PrefixCut := [⟨55,236065797,236065936⟩,
⟨128,550722813,550723122⟩]
theorem checked23631 : checkPrefixCuts (2^48) 3101294593 9 Manual.Count131072.C023631.packed 128 cuts23631 = true := by
 decide +kernel
def pointBounds23631 : List (Nat × Nat × Nat) := [(3101350912,102174790431021,102175172039930)]
theorem point_links_checked23631 : (cuts23631.take 1).map (fun c => (3101294593-1+2*2^9*c.k,102174554365224+c.lower,102174935973994+c.upper)) = pointBounds23631 := by
 decide +kernel
def cuts23632 : List PrefixCut := [⟨22,96473929,96473983⟩,
⟨117,495975320,495975596⟩,
⟨128,541079532,541079835⟩]
theorem checked23632 : checkPrefixCuts (2^48) 3101425665 9 Manual.Count131072.C023632.packed 128 cuts23632 = true := by
 decide +kernel
def pointBounds23632 : List (Nat × Nat × Nat) := [(3101448192,102175201561966,102175583171099),(3101545472,102175601063357,102175982672712)]
theorem point_links_checked23632 : (cuts23632.take 2).map (fun c => (3101425665-1+2*2^9*c.k,102175105088037+c.lower,102175486697116+c.upper)) = pointBounds23632 := by
 decide +kernel
def cuts23633 : List PrefixCut := [⟨84,353477209,353477408⟩,
⟨128,539604658,539604956⟩]
theorem checked23633 : checkPrefixCuts (2^48) 3101556737 9 Manual.Count131072.C023633.packed 128 cuts23633 = true := by
 decide +kernel
def pointBounds23633 : List (Nat × Nat × Nat) := [(3101642752,102175999644778,102176381254359)]
theorem point_links_checked23633 : (cuts23633.take 1).map (fun c => (3101556737-1+2*2^9*c.k,102175646167569+c.lower,102176027776951+c.upper)) = pointBounds23633 := by
 decide +kernel
def cuts23634 : List PrefixCut := [⟨51,216706648,216706768⟩,
⟨128,541941248,541941548⟩]
theorem checked23634 : checkPrefixCuts (2^48) 3101687809 9 Manual.Count131072.C023634.packed 128 cuts23634 = true := by
 decide +kernel
def pointBounds23634 : List (Nat × Nat × Nat) := [(3101740032,102176402478875,102176784088675)]
theorem point_links_checked23634 : (cuts23634.take 1).map (fun c => (3101687809-1+2*2^9*c.k,102176185772227+c.lower,102176567381907+c.upper)) = pointBounds23634 := by
 decide +kernel
def cuts23635 : List PrefixCut := [⟨18,76225666,76225708⟩,
⟨113,481666110,481666386⟩,
⟨128,543370326,543370639⟩]
theorem checked23635 : checkPrefixCuts (2^48) 3101818881 9 Manual.Count131072.C023635.packed 128 cuts23635 = true := by
 decide +kernel
def pointBounds23635 : List (Nat × Nat × Nat) := [(3101837312,102176803939141,102177185549163),(3101934592,102177209379585,102177590989841)]
theorem point_links_checked23635 : (cuts23635.take 2).map (fun c => (3101818881-1+2*2^9*c.k,102176727713475+c.lower,102177109323455+c.upper)) = pointBounds23635 := by
 decide +kernel
def cuts23636 : List PrefixCut := [⟨80,341636371,341636572⟩,
⟨128,545343543,545343862⟩]
theorem checked23636 : checkPrefixCuts (2^48) 3101949953 9 Manual.Count131072.C023636.packed 128 cuts23636 = true := by
 decide +kernel
def pointBounds23636 : List (Nat × Nat × Nat) := [(3102031872,102177612720172,102177994330666)]
theorem point_links_checked23636 : (cuts23636.take 1).map (fun c => (3101949953-1+2*2^9*c.k,102177271083801+c.lower,102177652694094+c.upper)) = pointBounds23636 := by
 decide +kernel
def cuts23637 : List PrefixCut := [⟨47,196626514,196626626⟩,
⟨128,538333912,538334213⟩]
theorem checked23637 : checkPrefixCuts (2^48) 3102081025 9 Manual.Count131072.C023637.packed 128 cuts23637 = true := by
 decide +kernel
def pointBounds23637 : List (Nat × Nat × Nat) := [(3102129152,102178013053858,102178394664582)]
theorem point_links_checked23637 : (cuts23637.take 1).map (fun c => (3102081025-1+2*2^9*c.k,102177816427344+c.lower,102178198037956+c.upper)) = pointBounds23637 := by
 decide +kernel
def cuts23638 : List PrefixCut := [⟨14,62606046,62606083⟩,
⟨109,463005239,463005498⟩,
⟨128,543210608,543210911⟩]
theorem checked23638 : checkPrefixCuts (2^48) 3102212097 9 Manual.Count131072.C023638.packed 128 cuts23638 = true := by
 decide +kernel
def pointBounds23638 : List (Nat × Nat × Nat) := [(3102226432,102178417367302,102178798978252),(3102323712,102178817766495,102179199377667)]
theorem point_links_checked23638 : (cuts23638.take 2).map (fun c => (3102212097-1+2*2^9*c.k,102178354761256+c.lower,102178736372169+c.upper)) = pointBounds23638 := by
 decide +kernel
def cuts23639 : List PrefixCut := [⟨76,323629016,323629197⟩,
⟨128,548177622,548177930⟩]
theorem checked23639 : checkPrefixCuts (2^48) 3102343169 9 Manual.Count131072.C023639.packed 128 cuts23639 = true := by
 decide +kernel
def pointBounds23639 : List (Nat × Nat × Nat) := [(3102420992,102179221600880,102179603212277)]
theorem point_links_checked23639 : (cuts23639.take 1).map (fun c => (3102343169-1+2*2^9*c.k,102178897971864+c.lower,102179279583080+c.upper)) = pointBounds23639 := by
 decide +kernel
def cuts23640 : List PrefixCut := [⟨43,186077578,186077685⟩,
⟨128,552418594,552418904⟩]
theorem checked23640 : checkPrefixCuts (2^48) 3102474241 9 Manual.Count131072.C023640.packed 128 cuts23640 = true := by
 decide +kernel
def pointBounds23640 : List (Nat × Nat × Nat) := [(3102518272,102179632227064,102180013838695)]
theorem point_links_checked23640 : (cuts23640.take 1).map (fun c => (3102474241-1+2*2^9*c.k,102179446149486+c.lower,102179827761010+c.upper)) = pointBounds23640 := by
 decide +kernel
def cuts23641 : List PrefixCut := [⟨10,42639322,42639345⟩,
⟨105,444530598,444530855⟩,
⟨128,539512999,539513313⟩]
theorem checked23641 : checkPrefixCuts (2^48) 3102605313 9 Manual.Count131072.C023641.packed 128 cuts23641 = true := by
 decide +kernel
def pointBounds23641 : List (Nat × Nat × Nat) := [(3102615552,102180041207402,102180422819259),(3102712832,102180443098678,102180824710769)]
theorem point_links_checked23641 : (cuts23641.take 2).map (fun c => (3102605313-1+2*2^9*c.k,102179998568080+c.lower,102180380179914+c.upper)) = pointBounds23641 := by
 decide +kernel
def cuts23642 : List PrefixCut := [⟨72,307349864,307350038⟩,
⟨128,549015335,549015645⟩]
theorem checked23642 : checkPrefixCuts (2^48) 3102736385 9 Manual.Count131072.C023642.packed 128 cuts23642 = true := by
 decide +kernel
def pointBounds23642 : List (Nat × Nat × Nat) := [(3102810112,102180845430943,102181227043265)]
theorem point_links_checked23642 : (cuts23642.take 1).map (fun c => (3102736385-1+2*2^9*c.k,102180538081079+c.lower,102180919693227+c.upper)) = pointBounds23642 := by
 decide +kernel
def cuts23643 : List PrefixCut := [⟨39,164917788,164917883⟩,
⟨128,539558132,539558445⟩]
theorem checked23643 : checkPrefixCuts (2^48) 3102867457 9 Manual.Count131072.C023643.packed 128 cuts23643 = true := by
 decide +kernel
def pointBounds23643 : List (Nat × Nat × Nat) := [(3102907392,102181252014202,102181633626755)]
theorem point_links_checked23643 : (cuts23643.take 1).map (fun c => (3102867457-1+2*2^9*c.k,102181087096414+c.lower,102181468708872+c.upper)) = pointBounds23643 := by
 decide +kernel
def cuts23644 : List PrefixCut := [⟨6,25943210,25943225⟩,
⟨101,424881424,424881665⟩,
⟨128,541168032,541168342⟩]
theorem checked23644 : checkPrefixCuts (2^48) 3102998529 9 Manual.Count131072.C023644.packed 128 cuts23644 = true := by
 decide +kernel
def pointBounds23644 : List (Nat × Nat × Nat) := [(3103004672,102181652597756,102182034210542),(3103101952,102182051535970,102182433148982)]
theorem point_links_checked23644 : (cuts23644.take 2).map (fun c => (3102998529-1+2*2^9*c.k,102181626654546+c.lower,102182008267317+c.upper)) = pointBounds23644 := by
 decide +kernel
def cuts23645 : List PrefixCut := [⟨68,290893402,290893564⟩,
⟨128,541961702,541962017⟩]
theorem checked23645 : checkPrefixCuts (2^48) 3103129601 9 Manual.Count131072.C023645.packed 128 cuts23645 = true := by
 decide +kernel
def pointBounds23645 : List (Nat × Nat × Nat) := [(3103199232,102182458715980,102182840329223)]
theorem point_links_checked23645 : (cuts23645.take 1).map (fun c => (3103129601-1+2*2^9*c.k,102182167822578+c.lower,102182549435659+c.upper)) = pointBounds23645 := by
 decide +kernel
def cuts23646 : List PrefixCut := [⟨35,151200947,151201037⟩,
⟨128,542392220,542392528⟩]
theorem checked23646 : checkPrefixCuts (2^48) 3103260673 9 Manual.Count131072.C023646.packed 128 cuts23646 = true := by
 decide +kernel
def pointBounds23646 : List (Nat × Nat × Nat) := [(3103296512,102182860985227,102183242598713)]
theorem point_links_checked23646 : (cuts23646.take 1).map (fun c => (3103260673-1+2*2^9*c.k,102182709784280+c.lower,102183091397676+c.upper)) = pointBounds23646 := by
 decide +kernel
def cuts23647 : List PrefixCut := [⟨2,7165228,7165233⟩,
⟨97,406597637,406597870⟩,
⟨128,535022824,535023134⟩]
theorem checked23647 : checkPrefixCuts (2^48) 3103391745 9 Manual.Count131072.C023647.packed 128 cuts23647 = true := by
 decide +kernel
def pointBounds23647 : List (Nat × Nat × Nat) := [(3103393792,102183259341728,102183640955437),(3103491072,102183658774137,102184040388074)]
theorem point_links_checked23647 : (cuts23647.take 2).map (fun c => (3103391745-1+2*2^9*c.k,102183252176500+c.lower,102183633790204+c.upper)) = pointBounds23647 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000113
