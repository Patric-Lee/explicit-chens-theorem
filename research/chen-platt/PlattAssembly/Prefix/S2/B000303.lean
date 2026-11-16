import PlattAssemblyKernel
import PlattCertificates.Count131072.C019696
import PlattCertificates.Count131072.C019697
import PlattCertificates.Count131072.C019698
import PlattCertificates.Count131072.C019699
import PlattCertificates.Count131072.C019700
import PlattCertificates.Count131072.C019701
import PlattCertificates.Count131072.C019702
import PlattCertificates.Count131072.C019703
import PlattCertificates.Count131072.C019704
import PlattCertificates.Count131072.C019705
import PlattCertificates.Count131072.C019706
import PlattCertificates.Count131072.C019707
import PlattCertificates.Count131072.C019708
import PlattCertificates.Count131072.C019709
import PlattCertificates.Count131072.C019710
import PlattCertificates.Count131072.C019711
import PlattCertificates.Count131072.C019712
import PlattCertificates.Count131072.C019713
import PlattCertificates.Count131072.C019714
import PlattCertificates.Count131072.C019715
import PlattCertificates.Count131072.C019716
import PlattCertificates.Count131072.C019717
import PlattCertificates.Count131072.C019718
import PlattCertificates.Count131072.C019719
import PlattCertificates.Count131072.C019720
import PlattCertificates.Count131072.C019721
import PlattCertificates.Count131072.C019722
import PlattCertificates.Count131072.C019723
import PlattCertificates.Count131072.C019724
import PlattCertificates.Count131072.C019725
import PlattCertificates.Count131072.C019726
import PlattCertificates.Count131072.C019727
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000303
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19696 : List PrefixCut := [⟨36,184852488,184852600⟩,
⟨115,589384999,589385351⟩,
⟨128,653503760,653504153⟩]
theorem checked19696 : checkPrefixCuts (2^48) 2585526273 9 Manual.Count131072.C019696.packed 128 cuts19696 = true := by
 decide +kernel
def pointBounds19696 : List (Nat × Nat × Nat) := [(2585563136,99822534501791,99822914754694),(2585644032,99822939034302,99823319287445)]
theorem point_links_checked19696 : (cuts19696.take 2).map (fun c => (2585526273-1+2*2^9*c.k,99822349649303+c.lower,99822729902094+c.upper)) = pointBounds19696 := by
 decide +kernel
def cuts19697 : List PrefixCut := [⟨66,343231369,343231576⟩,
⟨128,662288020,662288415⟩]
theorem checked19697 : checkPrefixCuts (2^48) 2585657345 9 Manual.Count131072.C019697.packed 128 cuts19697 = true := by
 decide +kernel
def pointBounds19697 : List (Nat × Nat × Nat) := [(2585724928,99823346384432,99823726637823)]
theorem point_links_checked19697 : (cuts19697.take 1).map (fun c => (2585657345-1+2*2^9*c.k,99823003153063+c.lower,99823383406247+c.upper)) = pointBounds19697 := by
 decide +kernel
def cuts19698 : List PrefixCut := [⟨17,83926592,83926643⟩,
⟨96,482434186,482434472⟩,
⟨128,644729154,644729536⟩]
theorem checked19698 : checkPrefixCuts (2^48) 2585788417 9 Manual.Count131072.C019698.packed 128 cuts19698 = true := by
 decide +kernel
def pointBounds19698 : List (Nat × Nat × Nat) := [(2585805824,99823749367675,99824129621305),(2585886720,99824147875269,99824528129134)]
theorem point_links_checked19698 : (cuts19698.take 2).map (fun c => (2585788417-1+2*2^9*c.k,99823665441083+c.lower,99824045694662+c.upper)) = pointBounds19698 := by
 decide +kernel
def cuts19699 : List PrefixCut := [⟨47,247193907,247194045⟩,
⟨126,649921550,649921930⟩,
⟨128,659173254,659173640⟩]
theorem checked19699 : checkPrefixCuts (2^48) 2585919489 9 Manual.Count131072.C019699.packed 128 cuts19699 = true := by
 decide +kernel
def pointBounds19699 : List (Nat × Nat × Nat) := [(2585967616,99824557364144,99824937618243),(2586048512,99824960091787,99825340346128)]
theorem point_links_checked19699 : (cuts19699.take 2).map (fun c => (2585919489-1+2*2^9*c.k,99824310170237+c.lower,99824690424198+c.upper)) = pointBounds19699 := by
 decide +kernel
def cuts19700 : List PrefixCut := [⟨77,397708183,397708412⟩,
⟨128,657833662,657834048⟩]
theorem checked19700 : checkPrefixCuts (2^48) 2586050561 9 Manual.Count131072.C019700.packed 128 cuts19700 = true := by
 decide +kernel
def pointBounds19700 : List (Nat × Nat × Nat) := [(2586129408,99825367051674,99825747306250)]
theorem point_links_checked19700 : (cuts19700.take 1).map (fun c => (2586050561-1+2*2^9*c.k,99824969343491+c.lower,99825349597838+c.upper)) = pointBounds19700 := by
 decide +kernel
def cuts19701 : List PrefixCut := [⟨28,145950961,145951050⟩,
⟨107,556368149,556368479⟩,
⟨128,667704248,667704645⟩]
theorem checked19701 : checkPrefixCuts (2^48) 2586181633 9 Manual.Count131072.C019701.packed 128 cuts19701 = true := by
 decide +kernel
def pointBounds19701 : List (Nat × Nat × Nat) := [(2586210304,99825773128114,99826153382936),(2586291200,99826183545302,99826563800365)]
theorem point_links_checked19701 : (cuts19701.take 2).map (fun c => (2586181633-1+2*2^9*c.k,99825627177153+c.lower,99826007431886+c.upper)) = pointBounds19701 := by
 decide +kernel
def cuts19702 : List PrefixCut := [⟨58,293409091,293409263⟩,
⟨128,648625311,648625697⟩]
theorem checked19702 : checkPrefixCuts (2^48) 2586312705 9 Manual.Count131072.C019702.packed 128 cuts19702 = true := by
 decide +kernel
def pointBounds19702 : List (Nat × Nat × Nat) := [(2586372096,99826588290492,99826968545794)]
theorem point_links_checked19702 : (cuts19702.take 1).map (fun c => (2586312705-1+2*2^9*c.k,99826294881401+c.lower,99826675136531+c.upper)) = pointBounds19702 := by
 decide +kernel
def cuts19703 : List PrefixCut := [⟨9,45924908,45924934⟩,
⟨88,453909490,453909756⟩,
⟨128,662957200,662957591⟩]
theorem checked19703 : checkPrefixCuts (2^48) 2586443777 9 Manual.Count131072.C019703.packed 128 cuts19703 = true := by
 decide +kernel
def pointBounds19703 : List (Nat × Nat × Nat) := [(2586452992,99826989431620,99827369687162),(2586533888,99827397416202,99827777671984)]
theorem point_links_checked19703 : (cuts19703.take 2).map (fun c => (2586443777-1+2*2^9*c.k,99826943506712+c.lower,99827323762228+c.upper)) = pointBounds19703 := by
 decide +kernel
def cuts19704 : List PrefixCut := [⟨39,206976858,206976979⟩,
⟨118,614065351,614065715⟩,
⟨128,664773688,664774082⟩]
theorem checked19704 : checkPrefixCuts (2^48) 2586574849 9 Manual.Count131072.C019704.packed 128 cuts19704 = true := by
 decide +kernel
def pointBounds19704 : List (Nat × Nat × Nat) := [(2586614784,99827813440770,99828193696798),(2586695680,99828220529263,99828600785534)]
theorem point_links_checked19704 : (cuts19704.take 2).map (fun c => (2586574849-1+2*2^9*c.k,99827606463912+c.lower,99827986719819+c.upper)) = pointBounds19704 := by
 decide +kernel
def cuts19705 : List PrefixCut := [⟨69,350926697,350926903⟩,
⟨128,651899945,651900332⟩]
theorem checked19705 : checkPrefixCuts (2^48) 2586705921 9 Manual.Count131072.C019705.packed 128 cuts19705 = true := by
 decide +kernel
def pointBounds19705 : List (Nat × Nat × Nat) := [(2586776576,99828622164297,99829002420804)]
theorem point_links_checked19705 : (cuts19705.take 1).map (fun c => (2586705921-1+2*2^9*c.k,99828271237600+c.lower,99828651493901+c.upper)) = pointBounds19705 := by
 decide +kernel
def cuts19706 : List PrefixCut := [⟨20,102390221,102390281⟩,
⟨99,506611523,506611823⟩,
⟨128,655348720,655349108⟩]
theorem checked19706 : checkPrefixCuts (2^48) 2586836993 9 Manual.Count131072.C019706.packed 128 cuts19706 = true := by
 decide +kernel
def pointBounds19706 : List (Nat × Nat × Nat) := [(2586857472,99829025527766,99829405784514),(2586938368,99829429749068,99829810006056)]
theorem point_links_checked19706 : (cuts19706.take 2).map (fun c => (2586836993-1+2*2^9*c.k,99828923137545+c.lower,99829303394233+c.upper)) = pointBounds19706 := by
 decide +kernel
def cuts19707 : List PrefixCut := [⟨50,256885888,256886044⟩,
⟨128,651725109,651725502⟩]
theorem checked19707 : checkPrefixCuts (2^48) 2586968065 9 Manual.Count131072.C019707.packed 128 cuts19707 = true := by
 decide +kernel
def pointBounds19707 : List (Nat × Nat × Nat) := [(2587019264,99829835372153,99830215629385)]
theorem point_links_checked19707 : (cuts19707.take 1).map (fun c => (2586968065-1+2*2^9*c.k,99829578486265+c.lower,99829958743341+c.upper)) = pointBounds19707 := by
 decide +kernel
def cuts19708 : List PrefixCut := [⟨1,5222371,5222374⟩,
⟨80,402551490,402551731⟩,
⟨128,651800740,651801130⟩]
theorem checked19708 : checkPrefixCuts (2^48) 2587099137 9 Manual.Count131072.C019708.packed 128 cuts19708 = true := by
 decide +kernel
def pointBounds19708 : List (Nat × Nat × Nat) := [(2587100160,99830235433745,99830615691217),(2587181056,99830632762864,99831013020574)]
theorem point_links_checked19708 : (cuts19708.take 2).map (fun c => (2587099137-1+2*2^9*c.k,99830230211374+c.lower,99830610468843+c.upper)) = pointBounds19708 := by
 decide +kernel
def cuts19709 : List PrefixCut := [⟨31,156335884,156335977⟩,
⟨110,562343508,562343844⟩,
⟨128,656119453,656119845⟩]
theorem checked19709 : checkPrefixCuts (2^48) 2587230209 9 Manual.Count131072.C019709.packed 128 cuts19709 = true := by
 decide +kernel
def pointBounds19709 : List (Nat × Nat × Nat) := [(2587261952,99831038347998,99831418605950),(2587342848,99831444355622,99831824613817)]
theorem point_links_checked19709 : (cuts19709.take 2).map (fun c => (2587230209-1+2*2^9*c.k,99830882012114+c.lower,99831262269973+c.upper)) = pointBounds19709 := by
 decide +kernel
def cuts19710 : List PrefixCut := [⟨61,313306828,313307017⟩,
⟨128,663048475,663048869⟩]
theorem checked19710 : checkPrefixCuts (2^48) 2587361281 9 Manual.Count131072.C019710.packed 128 cuts19710 = true := by
 decide +kernel
def pointBounds19710 : List (Nat × Nat × Nat) := [(2587423744,99831851438395,99832231696835)]
theorem point_links_checked19710 : (cuts19710.take 1).map (fun c => (2587361281-1+2*2^9*c.k,99831538131567+c.lower,99831918389818+c.upper)) = pointBounds19710 := by
 decide +kernel
def cuts19711 : List PrefixCut := [⟨12,62006100,62006136⟩,
⟨91,467540462,467540741⟩,
⟨128,664537749,664538146⟩]
theorem checked19711 : checkPrefixCuts (2^48) 2587492353 9 Manual.Count131072.C019711.packed 128 cuts19711 = true := by
 decide +kernel
def pointBounds19711 : List (Nat × Nat × Nat) := [(2587504640,99832263186142,99832643444823),(2587585536,99832668720504,99833048979428)]
theorem point_links_checked19711 : (cuts19711.take 2).map (fun c => (2587492353-1+2*2^9*c.k,99832201180042+c.lower,99832581438687+c.upper)) = pointBounds19711 := by
 decide +kernel
def cuts19712 : List PrefixCut := [⟨42,214180885,214181011⟩,
⟨121,622082953,622083323⟩,
⟨128,657325090,657325481⟩]
theorem checked19712 : checkPrefixCuts (2^48) 2587623425 9 Manual.Count131072.C019712.packed 128 cuts19712 = true := by
 decide +kernel
def pointBounds19712 : List (Nat × Nat × Nat) := [(2587666432,99833079898676,99833460157844),(2587747328,99833487800744,99833868060156)]
theorem point_links_checked19712 : (cuts19712.take 2).map (fun c => (2587623425-1+2*2^9*c.k,99832865717791+c.lower,99833245976833+c.upper)) = pointBounds19712 := by
 decide +kernel
def cuts19713 : List PrefixCut := [⟨72,373299751,373299973⟩,
⟨128,661642549,661642940⟩]
theorem checked19713 : checkPrefixCuts (2^48) 2587754497 9 Manual.Count131072.C019713.packed 128 cuts19713 = true := by
 decide +kernel
def pointBounds19713 : List (Nat × Nat × Nat) := [(2587828224,99833896342632,99834276602287)]
theorem point_links_checked19713 : (cuts19713.take 1).map (fun c => (2587754497-1+2*2^9*c.k,99833523042881+c.lower,99833903302314+c.upper)) = pointBounds19713 := by
 decide +kernel
def cuts19714 : List PrefixCut := [⟨23,116161935,116162003⟩,
⟨102,523481852,523482160⟩,
⟨128,658781036,658781422⟩]
theorem checked19714 : checkPrefixCuts (2^48) 2587885569 9 Manual.Count131072.C019714.packed 128 cuts19714 = true := by
 decide +kernel
def pointBounds19714 : List (Nat × Nat × Nat) := [(2587909120,99834300847365,99834681107257),(2587990016,99834708167282,99835088427414)]
theorem point_links_checked19714 : (cuts19714.take 2).map (fun c => (2587885569-1+2*2^9*c.k,99834184685430+c.lower,99834564945254+c.upper)) = pointBounds19714 := by
 decide +kernel
def cuts19715 : List PrefixCut := [⟨53,274835785,274835944⟩,
⟨128,659074131,659074516⟩]
theorem checked19715 : checkPrefixCuts (2^48) 2588016641 9 Manual.Count131072.C019715.packed 128 cuts19715 = true := by
 decide +kernel
def pointBounds19715 : List (Nat × Nat × Nat) := [(2588070912,99835118302251,99835498562620)]
theorem point_links_checked19715 : (cuts19715.take 1).map (fun c => (2588016641-1+2*2^9*c.k,99834843466466+c.lower,99835223726676+c.upper)) = pointBounds19715 := by
 decide +kernel
def cuts19716 : List PrefixCut := [⟨4,19575945,19575957⟩,
⟨83,423595142,423595390⟩,
⟨128,652950586,652950969⟩]
theorem checked19716 : checkPrefixCuts (2^48) 2588147713 9 Manual.Count131072.C019716.packed 128 cuts19716 = true := by
 decide +kernel
def pointBounds19716 : List (Nat × Nat × Nat) := [(2588151808,99835522116542,99835902377149),(2588232704,99835926135739,99836306396582)]
theorem point_links_checked19716 : (cuts19716.take 2).map (fun c => (2588147713-1+2*2^9*c.k,99835502540597+c.lower,99835882801192+c.upper)) = pointBounds19716 := by
 decide +kernel
def cuts19717 : List PrefixCut := [⟨34,174107340,174107442⟩,
⟨113,574947541,574947885⟩,
⟨128,654331138,654331529⟩]
theorem checked19717 : checkPrefixCuts (2^48) 2588278785 9 Manual.Count131072.C019717.packed 128 cuts19717 = true := by
 decide +kernel
def pointBounds19717 : List (Nat × Nat × Nat) := [(2588313600,99836329598523,99836709859603),(2588394496,99836730438724,99837110700046)]
theorem point_links_checked19717 : (cuts19717.take 2).map (fun c => (2588278785-1+2*2^9*c.k,99836155491183+c.lower,99836535752161+c.upper)) = pointBounds19717 := by
 decide +kernel
def cuts19718 : List PrefixCut := [⟨64,328294973,328295167⟩,
⟨128,657451576,657451966⟩]
theorem checked19718 : checkPrefixCuts (2^48) 2588409857 9 Manual.Count131072.C019718.packed 128 cuts19718 = true := by
 decide +kernel
def pointBounds19718 : List (Nat × Nat × Nat) := [(2588475392,99837138117294,99837518378857)]
theorem point_links_checked19718 : (cuts19718.take 1).map (fun c => (2588409857-1+2*2^9*c.k,99836809822321+c.lower,99837190083690+c.upper)) = pointBounds19718 := by
 decide +kernel
def cuts19719 : List PrefixCut := [⟨15,79705317,79705364⟩,
⟨94,487249628,487249923⟩,
⟨128,657309670,657310064⟩]
theorem checked19719 : checkPrefixCuts (2^48) 2588540929 9 Manual.Count131072.C019719.packed 128 cuts19719 = true := by
 decide +kernel
def pointBounds19719 : List (Nat × Nat × Nat) := [(2588556288,99837546979214,99837927241020),(2588637184,99837954523525,99838334785579)]
theorem point_links_checked19719 : (cuts19719.take 2).map (fun c => (2588540929-1+2*2^9*c.k,99837467273897+c.lower,99837847535656+c.upper)) = pointBounds19719 := by
 decide +kernel
def cuts19720 : List PrefixCut := [⟨45,231599911,231600047⟩,
⟨125,638466305,638466678⟩,
⟨128,653579479,653579862⟩]
theorem checked19720 : checkPrefixCuts (2^48) 2588672001 9 Manual.Count131072.C019720.packed 128 cuts19720 = true := by
 decide +kernel
def pointBounds19720 : List (Nat × Nat × Nat) := [(2588718080,99838356183478,99838736445767),(2588800000,99838763049872,99839143312398)]
theorem point_links_checked19720 : (cuts19720.take 2).map (fun c => (2588672001-1+2*2^9*c.k,99838124583567+c.lower,99838504845720+c.upper)) = pointBounds19720 := by
 decide +kernel
def cuts19721 : List PrefixCut := [⟨77,399459982,399460219⟩,
⟨128,661700829,661701221⟩]
theorem checked19721 : checkPrefixCuts (2^48) 2588803073 9 Manual.Count131072.C019721.packed 128 cuts19721 = true := by
 decide +kernel
def pointBounds19721 : List (Nat × Nat × Nat) := [(2588881920,99839177623028,99839557885801)]
theorem point_links_checked19721 : (cuts19721.take 1).map (fun c => (2588803073-1+2*2^9*c.k,99838778163046+c.lower,99839158425582+c.upper)) = pointBounds19721 := by
 decide +kernel
def cuts19722 : List PrefixCut := [⟨29,152210345,152210434⟩,
⟨109,559581656,559581989⟩,
⟨128,655361522,655361909⟩]
theorem checked19722 : checkPrefixCuts (2^48) 2588934145 9 Manual.Count131072.C019722.packed 128 cuts19722 = true := by
 decide +kernel
def pointBounds19722 : List (Nat × Nat × Nat) := [(2588963840,99839592074220,99839972337237),(2589045760,99839999445531,99840379708792)]
theorem point_links_checked19722 : (cuts19722.take 2).map (fun c => (2588934145-1+2*2^9*c.k,99839439863875+c.lower,99839820126803+c.upper)) = pointBounds19722 := by
 decide +kernel
def cuts19723 : List PrefixCut := [⟨61,308534564,308534746⟩,
⟨128,654567247,654567632⟩]
theorem checked19723 : checkPrefixCuts (2^48) 2589065217 9 Manual.Count131072.C019723.packed 128 cuts19723 = true := by
 decide +kernel
def pointBounds19723 : List (Nat × Nat × Nat) := [(2589127680,99840403759961,99840784023458)]
theorem point_links_checked19723 : (cuts19723.take 1).map (fun c => (2589065217-1+2*2^9*c.k,99840095225397+c.lower,99840475488712+c.upper)) = pointBounds19723 := by
 decide +kernel
def cuts19724 : List PrefixCut := [⟨13,70227323,70227364⟩,
⟨93,484517397,484517681⟩,
⟨128,666600850,666601244⟩]
theorem checked19724 : checkPrefixCuts (2^48) 2589196289 9 Manual.Count131072.C019724.packed 128 cuts19724 = true := by
 decide +kernel
def pointBounds19724 : List (Nat × Nat × Nat) := [(2589209600,99840820019967,99841200283708),(2589291520,99841234310041,99841614574025)]
theorem point_links_checked19724 : (cuts19724.take 2).map (fun c => (2589196289-1+2*2^9*c.k,99840749792644+c.lower,99841130056344+c.upper)) = pointBounds19724 := by
 decide +kernel
def cuts19725 : List PrefixCut := [⟨45,238715823,238715960⟩,
⟨125,641674674,641675049⟩,
⟨128,657436226,657436610⟩]
theorem checked19725 : checkPrefixCuts (2^48) 2589327361 9 Manual.Count131072.C019725.packed 128 cuts19725 = true := by
 decide +kernel
def pointBounds19725 : List (Nat × Nat × Nat) := [(2589373440,99841655109317,99842035373548),(2589455360,99842058068168,99842438332637)]
theorem point_links_checked19725 : (cuts19725.take 2).map (fun c => (2589327361-1+2*2^9*c.k,99841416393494+c.lower,99841796657588+c.upper)) = pointBounds19725 := by
 decide +kernel
def cuts19726 : List PrefixCut := [⟨77,393380401,393380636⟩,
⟨128,660120107,660120498⟩]
theorem checked19726 : checkPrefixCuts (2^48) 2589458433 9 Manual.Count131072.C019726.packed 128 cuts19726 = true := by
 decide +kernel
def pointBounds19726 : List (Nat × Nat × Nat) := [(2589537280,99842467210121,99842847474834)]
theorem point_links_checked19726 : (cuts19726.take 1).map (fun c => (2589458433-1+2*2^9*c.k,99842073829720+c.lower,99842454094198+c.upper)) = pointBounds19726 := by
 decide +kernel
def cuts19727 : List PrefixCut := [⟨29,149997955,149998042⟩,
⟨109,555309719,555310047⟩,
⟨128,658347546,658347930⟩]
theorem checked19727 : checkPrefixCuts (2^48) 2589589505 9 Manual.Count131072.C019727.packed 128 cuts19727 = true := by
 decide +kernel
def pointBounds19727 : List (Nat × Nat × Nat) := [(2589619200,99842883947782,99843264212738),(2589701120,99843289259546,99843669524743)]
theorem point_links_checked19727 : (cuts19727.take 2).map (fun c => (2589589505-1+2*2^9*c.k,99842733949827+c.lower,99843114214696+c.upper)) = pointBounds19727 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000303
