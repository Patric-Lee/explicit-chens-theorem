import PlattAssemblyKernel
import PlattCertificates.Count131072.C019632
import PlattCertificates.Count131072.C019633
import PlattCertificates.Count131072.C019634
import PlattCertificates.Count131072.C019635
import PlattCertificates.Count131072.C019636
import PlattCertificates.Count131072.C019637
import PlattCertificates.Count131072.C019638
import PlattCertificates.Count131072.C019639
import PlattCertificates.Count131072.C019640
import PlattCertificates.Count131072.C019641
import PlattCertificates.Count131072.C019642
import PlattCertificates.Count131072.C019643
import PlattCertificates.Count131072.C019644
import PlattCertificates.Count131072.C019645
import PlattCertificates.Count131072.C019646
import PlattCertificates.Count131072.C019647
import PlattCertificates.Count131072.C019648
import PlattCertificates.Count131072.C019649
import PlattCertificates.Count131072.C019650
import PlattCertificates.Count131072.C019651
import PlattCertificates.Count131072.C019652
import PlattCertificates.Count131072.C019653
import PlattCertificates.Count131072.C019654
import PlattCertificates.Count131072.C019655
import PlattCertificates.Count131072.C019656
import PlattCertificates.Count131072.C019657
import PlattCertificates.Count131072.C019658
import PlattCertificates.Count131072.C019659
import PlattCertificates.Count131072.C019660
import PlattCertificates.Count131072.C019661
import PlattCertificates.Count131072.C019662
import PlattCertificates.Count131072.C019663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000301
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19632 : List PrefixCut := [⟨12,65313385,65313423⟩,
⟨91,467889934,467890213⟩,
⟨128,663931240,663931633⟩]
theorem checked19632 : checkPrefixCuts (2^48) 2577137665 9 Manual.Count131072.C019632.packed 128 cuts19632 = true := by
 decide +kernel
def pointBounds19632 : List (Nat × Nat × Nat) := [(2577149952,99780195629086,99780575856996),(2577230848,99780598205635,99780978433786)]
theorem point_links_checked19632 : (cuts19632.take 2).map (fun c => (2577137665-1+2*2^9*c.k,99780130315701+c.lower,99780510543573+c.upper)) = pointBounds19632 := by
 decide +kernel
def cuts19633 : List PrefixCut := [⟨42,221266560,221266692⟩,
⟨121,632554770,632555143⟩,
⟨128,670341089,670341484⟩]
theorem checked19633 : checkPrefixCuts (2^48) 2577268737 9 Manual.Count131072.C019633.packed 128 cuts19633 = true := by
 decide +kernel
def pointBounds19633 : List (Nat × Nat × Nat) := [(2577311744,99781015513501,99781395741898),(2577392640,99781426801711,99781807030349)]
theorem point_links_checked19633 : (cuts19633.take 2).map (fun c => (2577268737-1+2*2^9*c.k,99780794246941+c.lower,99781174475206+c.upper)) = pointBounds19633 := by
 decide +kernel
def cuts19634 : List PrefixCut := [⟨72,367045740,367045959⟩,
⟨128,652397156,652397542⟩]
theorem checked19634 : checkPrefixCuts (2^48) 2577399809 9 Manual.Count131072.C019634.packed 128 cuts19634 = true := by
 decide +kernel
def pointBounds19634 : List (Nat × Nat × Nat) := [(2577473536,99781831633770,99782211862649)]
theorem point_links_checked19634 : (cuts19634.take 1).map (fun c => (2577399809-1+2*2^9*c.k,99781464588030+c.lower,99781844816690+c.upper)) = pointBounds19634 := by
 decide +kernel
def cuts19635 : List PrefixCut := [⟨23,119904669,119904739⟩,
⟨102,518377616,518377924⟩,
⟨128,652582349,652582734⟩]
theorem checked19635 : checkPrefixCuts (2^48) 2577530881 9 Manual.Count131072.C019635.packed 128 cuts19635 = true := by
 decide +kernel
def pointBounds19635 : List (Nat × Nat × Nat) := [(2577554432,99782236889855,99782617118971),(2577635328,99782635362802,99783015592156)]
theorem point_links_checked19635 : (cuts19635.take 2).map (fun c => (2577530881-1+2*2^9*c.k,99782116985186+c.lower,99782497214232+c.upper)) = pointBounds19635 := by
 decide +kernel
def cuts19636 : List PrefixCut := [⟨53,276158226,276158393⟩,
⟨128,674169723,674170126⟩]
theorem checked19636 : checkPrefixCuts (2^48) 2577661953 9 Manual.Count131072.C019636.packed 128 cuts19636 = true := by
 decide +kernel
def pointBounds19636 : List (Nat × Nat × Nat) := [(2577716224,99783045725761,99783425955359)]
theorem point_links_checked19636 : (cuts19636.take 1).map (fun c => (2577661953-1+2*2^9*c.k,99782769567535+c.lower,99783149796966+c.upper)) = pointBounds19636 := by
 decide +kernel
def cuts19637 : List PrefixCut := [⟨4,22384383,22384395⟩,
⟨83,422676161,422676410⟩,
⟨128,660923545,660923934⟩]
theorem checked19637 : checkPrefixCuts (2^48) 2577793025 9 Manual.Count131072.C019637.packed 128 cuts19637 = true := by
 decide +kernel
def pointBounds19637 : List (Nat × Nat × Nat) := [(2577797120,99783466121641,99783846351487),(2577878016,99783866413419,99784246643502)]
theorem point_links_checked19637 : (cuts19637.take 2).map (fun c => (2577793025-1+2*2^9*c.k,99783443737258+c.lower,99783823967092+c.upper)) = pointBounds19637 := by
 decide +kernel
def cuts19638 : List PrefixCut := [⟨34,172841305,172841406⟩,
⟨113,584572156,584572500⟩,
⟨128,662855234,662855626⟩]
theorem checked19638 : checkPrefixCuts (2^48) 2577924097 9 Manual.Count131072.C019638.packed 128 cuts19638 = true := by
 decide +kernel
def pointBounds19638 : List (Nat × Nat × Nat) := [(2577958912,99784277502108,99784657732432),(2578039808,99784689232959,99785069463526)]
theorem point_links_checked19638 : (cuts19638.take 2).map (fun c => (2577924097-1+2*2^9*c.k,99784104660803+c.lower,99784484891026+c.upper)) = pointBounds19638 := by
 decide +kernel
def cuts19639 : List PrefixCut := [⟨64,323827064,323827254⟩,
⟨128,655834172,655834554⟩]
theorem checked19639 : checkPrefixCuts (2^48) 2578055169 9 Manual.Count131072.C019639.packed 128 cuts19639 = true := by
 decide +kernel
def pointBounds19639 : List (Nat × Nat × Nat) := [(2578120704,99785091343101,99785471573906)]
theorem point_links_checked19639 : (cuts19639.take 1).map (fun c => (2578055169-1+2*2^9*c.k,99784767516037+c.lower,99785147746652+c.upper)) = pointBounds19639 := by
 decide +kernel
def cuts19640 : List PrefixCut := [⟨15,80243781,80243830⟩,
⟨94,484948787,484949080⟩,
⟨128,661587037,661587434⟩]
theorem checked19640 : checkPrefixCuts (2^48) 2578186241 9 Manual.Count131072.C019640.packed 128 cuts19640 = true := by
 decide +kernel
def pointBounds19640 : List (Nat × Nat × Nat) := [(2578201600,99785503593990,99785883825036),(2578282496,99785908298996,99786288530286)]
theorem point_links_checked19640 : (cuts19640.take 2).map (fun c => (2578186241-1+2*2^9*c.k,99785423350209+c.lower,99785803581206+c.upper)) = pointBounds19640 := by
 decide +kernel
def cuts19641 : List PrefixCut := [⟨45,232966706,232966844⟩,
⟨124,643541234,643541616⟩,
⟨128,664719154,664719548⟩]
theorem checked19641 : checkPrefixCuts (2^48) 2578317313 9 Manual.Count131072.C019641.packed 128 cuts19641 = true := by
 decide +kernel
def pointBounds19641 : List (Nat × Nat × Nat) := [(2578363392,99786317903952,99786698135484),(2578444288,99786728478480,99787108710256)]
theorem point_links_checked19641 : (cuts19641.take 2).map (fun c => (2578317313-1+2*2^9*c.k,99786084937246+c.lower,99786465168640+c.upper)) = pointBounds19641 := by
 decide +kernel
def cuts19642 : List PrefixCut := [⟨75,382833978,382834202⟩,
⟨128,658353954,658354338⟩]
theorem checked19642 : checkPrefixCuts (2^48) 2578448385 9 Manual.Count131072.C019642.packed 128 cuts19642 = true := by
 decide +kernel
def pointBounds19642 : List (Nat × Nat × Nat) := [(2578525184,99787132490378,99787512722390)]
theorem point_links_checked19642 : (cuts19642.take 1).map (fun c => (2578448385-1+2*2^9*c.k,99786749656400+c.lower,99787129888188+c.upper)) = pointBounds19642 := by
 decide +kernel
def cuts19643 : List PrefixCut := [⟨26,134919704,134919783⟩,
⟨105,534758335,534758652⟩,
⟨128,654172657,654173044⟩]
theorem checked19643 : checkPrefixCuts (2^48) 2578579457 9 Manual.Count131072.C019643.packed 128 cuts19643 = true := by
 decide +kernel
def pointBounds19643 : List (Nat × Nat × Nat) := [(2578606080,99787542930058,99787923162309),(2578686976,99787942768689,99788323001178)]
theorem point_links_checked19643 : (cuts19643.take 2).map (fun c => (2578579457-1+2*2^9*c.k,99787408010354+c.lower,99787788242526+c.upper)) = pointBounds19643 := by
 decide +kernel
def cuts19644 : List PrefixCut := [⟨56,289253176,289253347⟩,
⟨128,652283960,652284344⟩]
theorem checked19644 : checkPrefixCuts (2^48) 2578710529 9 Manual.Count131072.C019644.packed 128 cuts19644 = true := by
 decide +kernel
def pointBounds19644 : List (Nat × Nat × Nat) := [(2578767872,99788351436187,99788731668917)]
theorem point_links_checked19644 : (cuts19644.take 1).map (fun c => (2578710529-1+2*2^9*c.k,99788062183011+c.lower,99788442415570+c.upper)) = pointBounds19644 := by
 decide +kernel
def cuts19645 : List PrefixCut := [⟨7,33944920,33944941⟩,
⟨86,439094045,439094302⟩,
⟨128,658144379,658144765⟩]
theorem checked19645 : checkPrefixCuts (2^48) 2578841601 9 Manual.Count131072.C019645.packed 128 cuts19645 = true := by
 decide +kernel
def pointBounds19645 : List (Nat × Nat × Nat) := [(2578848768,99788748411891,99789128644855),(2578929664,99789153561016,99789533794216)]
theorem point_links_checked19645 : (cuts19645.take 2).map (fun c => (2578841601-1+2*2^9*c.k,99788714466971+c.lower,99789094699914+c.upper)) = pointBounds19645 := by
 decide +kernel
def cuts19646 : List PrefixCut := [⟨37,190670115,190670228⟩,
⟨116,600705078,600705434⟩,
⟨128,663240560,663240953⟩]
theorem checked19646 : checkPrefixCuts (2^48) 2578972673 9 Manual.Count131072.C019646.packed 128 cuts19646 = true := by
 decide +kernel
def pointBounds19646 : List (Nat × Nat × Nat) := [(2579010560,99789563281465,99789943514907),(2579091456,99789973316428,99790353550113)]
theorem point_links_checked19646 : (cuts19646.take 2).map (fun c => (2578972673-1+2*2^9*c.k,99789372611350+c.lower,99789752844679+c.upper)) = pointBounds19646 := by
 decide +kernel
def cuts19647 : List PrefixCut := [⟨67,345522281,345522486⟩,
⟨128,656986407,656986796⟩]
theorem checked19647 : checkPrefixCuts (2^48) 2579103745 9 Manual.Count131072.C019647.packed 128 cuts19647 = true := by
 decide +kernel
def pointBounds19647 : List (Nat × Nat × Nat) := [(2579172352,99790381374191,99790761608118)]
theorem point_links_checked19647 : (cuts19647.take 1).map (fun c => (2579103745-1+2*2^9*c.k,99790035851910+c.lower,99790416085632+c.upper)) = pointBounds19647 := by
 decide +kernel
def cuts19648 : List PrefixCut := [⟨18,96908127,96908182⟩,
⟨97,500793365,500793663⟩,
⟨128,655970956,655971344⟩]
theorem checked19648 : checkPrefixCuts (2^48) 2579234817 9 Manual.Count131072.C019648.packed 128 cuts19648 = true := by
 decide +kernel
def pointBounds19648 : List (Nat × Nat × Nat) := [(2579253248,99790789746444,99791169980610),(2579334144,99791193631682,99791573866091)]
theorem point_links_checked19648 : (cuts19648.take 2).map (fun c => (2579234817-1+2*2^9*c.k,99790692838317+c.lower,99791073072428+c.upper)) = pointBounds19648 := by
 decide +kernel
def cuts19649 : List PrefixCut := [⟨48,244766438,244766578⟩,
⟨127,653864062,653864442⟩,
⟨128,659101826,659102210⟩]
theorem checked19649 : checkPrefixCuts (2^48) 2579365889 9 Manual.Count131072.C019649.packed 128 cuts19649 = true := by
 decide +kernel
def pointBounds19649 : List (Nat × Nat × Nat) := [(2579415040,99791593575711,99791973810350),(2579495936,99792002673335,99792382908214)]
theorem point_links_checked19649 : (cuts19649.take 2).map (fun c => (2579365889-1+2*2^9*c.k,99791348809273+c.lower,99791729043772+c.upper)) = pointBounds19649 := by
 decide +kernel
def cuts19650 : List PrefixCut := [⟨78,410285150,410285388⟩,
⟨128,669325593,669325981⟩]
theorem checked19650 : checkPrefixCuts (2^48) 2579496961 9 Manual.Count131072.C019650.packed 128 cuts19650 = true := by
 decide +kernel
def pointBounds19650 : List (Nat × Nat × Nat) := [(2579576832,99792418196249,99792798431370)]
theorem point_links_checked19650 : (cuts19650.take 1).map (fun c => (2579496961-1+2*2^9*c.k,99792007911099+c.lower,99792388145982+c.upper)) = pointBounds19650 := by
 decide +kernel
def cuts19651 : List PrefixCut := [⟨29,149267796,149267885⟩,
⟨108,560836586,560836915⟩,
⟨128,663290331,663290719⟩]
theorem checked19651 : checkPrefixCuts (2^48) 2579628033 9 Manual.Count131072.C019651.packed 128 cuts19651 = true := by
 decide +kernel
def pointBounds19651 : List (Nat × Nat × Nat) := [(2579657728,99792826504488,99793206739848),(2579738624,99793238073278,99793618308878)]
theorem point_links_checked19651 : (cuts19651.take 2).map (fun c => (2579628033-1+2*2^9*c.k,99792677236692+c.lower,99793057471963+c.upper)) = pointBounds19651 := by
 decide +kernel
def cuts19652 : List PrefixCut := [⟨59,301355484,301355662⟩,
⟨128,659765188,659765577⟩]
theorem checked19652 : checkPrefixCuts (2^48) 2579759105 9 Manual.Count131072.C019652.packed 128 cuts19652 = true := by
 decide +kernel
def pointBounds19652 : List (Nat × Nat × Nat) := [(2579819520,99793641882507,99794022118344)]
theorem point_links_checked19652 : (cuts19652.take 1).map (fun c => (2579759105-1+2*2^9*c.k,99793340527023+c.lower,99793720762682+c.upper)) = pointBounds19652 := by
 decide +kernel
def cuts19653 : List PrefixCut := [⟨10,49860174,49860205⟩,
⟨89,460735663,460735936⟩,
⟨128,657658867,657659252⟩]
theorem checked19653 : checkPrefixCuts (2^48) 2579890177 9 Manual.Count131072.C019653.packed 128 cuts19653 = true := by
 decide +kernel
def pointBounds19653 : List (Nat × Nat × Nat) := [(2579900416,99794050152385,99794430388464),(2579981312,99794461027874,99794841264195)]
theorem point_links_checked19653 : (cuts19653.take 2).map (fun c => (2579890177-1+2*2^9*c.k,99794000292211+c.lower,99794380528259+c.upper)) = pointBounds19653 := by
 decide +kernel
def cuts19654 : List PrefixCut := [⟨40,203466003,203466125⟩,
⟨119,607115508,607115869⟩,
⟨128,654243488,654243877⟩]
theorem checked19654 : checkPrefixCuts (2^48) 2580021249 9 Manual.Count131072.C019654.packed 128 cuts19654 = true := by
 decide +kernel
def pointBounds19654 : List (Nat × Nat × Nat) := [(2580062208,99794861417081,99795241653636),(2580143104,99795265066586,99795645303380)]
theorem point_links_checked19654 : (cuts19654.take 2).map (fun c => (2580021249-1+2*2^9*c.k,99794657951078+c.lower,99795038187511+c.upper)) = pointBounds19654 := by
 decide +kernel
def cuts19655 : List PrefixCut := [⟨70,357163366,357163581⟩,
⟨128,664137235,664137633⟩]
theorem checked19655 : checkPrefixCuts (2^48) 2580152321 9 Manual.Count131072.C019655.packed 128 cuts19655 = true := by
 decide +kernel
def pointBounds19655 : List (Nat × Nat × Nat) := [(2580224000,99795669357932,99796049594969)]
theorem point_links_checked19655 : (cuts19655.take 1).map (fun c => (2580152321-1+2*2^9*c.k,99795312194566+c.lower,99795692431388+c.upper)) = pointBounds19655 := by
 decide +kernel
def cuts19656 : List PrefixCut := [⟨21,109304539,109304603⟩,
⟨100,516624901,516625204⟩,
⟨128,657776867,657777256⟩]
theorem checked19656 : checkPrefixCuts (2^48) 2580283393 9 Manual.Count131072.C019656.packed 128 cuts19656 = true := by
 decide +kernel
def pointBounds19656 : List (Nat × Nat × Nat) := [(2580304896,99796085636340,99796465873624),(2580385792,99796492956702,99796873194225)]
theorem point_links_checked19656 : (cuts19656.take 2).map (fun c => (2580283393-1+2*2^9*c.k,99795976331801+c.lower,99796356569021+c.upper)) = pointBounds19656 := by
 decide +kernel
def cuts19657 : List PrefixCut := [⟨51,266919193,266919349⟩,
⟨128,666469666,666470060⟩]
theorem checked19657 : checkPrefixCuts (2^48) 2580414465 9 Manual.Count131072.C019657.packed 128 cuts19657 = true := by
 decide +kernel
def pointBounds19657 : List (Nat × Nat × Nat) := [(2580466688,99796901027861,99797281265626)]
theorem point_links_checked19657 : (cuts19657.take 1).map (fun c => (2580414465-1+2*2^9*c.k,99796634108668+c.lower,99797014346277+c.upper)) = pointBounds19657 := by
 decide +kernel
def cuts19658 : List PrefixCut := [⟨2,9271434,9271440⟩,
⟨81,414262971,414263220⟩,
⟨128,658037142,658037534⟩]
theorem checked19658 : checkPrefixCuts (2^48) 2580545537 9 Manual.Count131072.C019658.packed 128 cuts19658 = true := by
 decide +kernel
def pointBounds19658 : List (Nat × Nat × Nat) := [(2580547584,99797309849768,99797690087777),(2580628480,99797714841305,99798095079557)]
theorem point_links_checked19658 : (cuts19658.take 2).map (fun c => (2580545537-1+2*2^9*c.k,99797300578334+c.lower,99797680816337+c.upper)) = pointBounds19658 := by
 decide +kernel
def cuts19659 : List PrefixCut := [⟨32,168403311,168403409⟩,
⟨111,572933086,572933428⟩,
⟨128,655604369,655604763⟩]
theorem checked19659 : checkPrefixCuts (2^48) 2580676609 9 Manual.Count131072.C019659.packed 128 cuts19659 = true := by
 decide +kernel
def pointBounds19659 : List (Nat × Nat × Nat) := [(2580709376,99798127018787,99798507257280),(2580790272,99798531548562,99798911787299)]
theorem point_links_checked19659 : (cuts19659.take 2).map (fun c => (2580676609-1+2*2^9*c.k,99797958615476+c.lower,99798338853871+c.upper)) = pointBounds19659 := by
 decide +kernel
def cuts19660 : List PrefixCut := [⟨62,321409557,321409743⟩,
⟨128,659170108,659170491⟩]
theorem checked19660 : checkPrefixCuts (2^48) 2580807681 9 Manual.Count131072.C019660.packed 128 cuts19660 = true := by
 decide +kernel
def pointBounds19660 : List (Nat × Nat × Nat) := [(2580871168,99798935629402,99799315868377)]
theorem point_links_checked19660 : (cuts19660.take 1).map (fun c => (2580807681-1+2*2^9*c.k,99798614219845+c.lower,99798994458634+c.upper)) = pointBounds19660 := by
 decide +kernel
def cuts19661 : List PrefixCut := [⟨13,68052713,68052753⟩,
⟨92,473307933,473308211⟩,
⟨128,653574770,653575155⟩]
theorem checked19661 : checkPrefixCuts (2^48) 2580938753 9 Manual.Count131072.C019661.packed 128 cuts19661 = true := by
 decide +kernel
def pointBounds19661 : List (Nat × Nat × Nat) := [(2580952064,99799341442666,99799721681878),(2581032960,99799746697886,99800126937336)]
theorem point_links_checked19661 : (cuts19661.take 2).map (fun c => (2580938753-1+2*2^9*c.k,99799273389953+c.lower,99799653629125+c.upper)) = pointBounds19661 := by
 decide +kernel
def cuts19662 : List PrefixCut := [⟨43,218759631,218759762⟩,
⟨122,628787663,628788043⟩,
⟨128,660847824,660848221⟩]
theorem checked19662 : checkPrefixCuts (2^48) 2581069825 9 Manual.Count131072.C019662.packed 128 cuts19662 = true := by
 decide +kernel
def pointBounds19662 : List (Nat × Nat × Nat) := [(2581113856,99800145724354,99800525964042),(2581194752,99800555752386,99800935992323)]
theorem point_links_checked19662 : (cuts19662.take 2).map (fun c => (2581069825-1+2*2^9*c.k,99799926964723+c.lower,99800307204280+c.upper)) = pointBounds19662 := by
 decide +kernel
def cuts19663 : List PrefixCut := [⟨73,382316934,382317155⟩,
⟨128,668120425,668120808⟩]
theorem checked19663 : checkPrefixCuts (2^48) 2581200897 9 Manual.Count131072.C019663.packed 128 cuts19663 = true := by
 decide +kernel
def pointBounds19663 : List (Nat × Nat × Nat) := [(2581275648,99800970129481,99801350369656)]
theorem point_links_checked19663 : (cuts19663.take 1).map (fun c => (2581200897-1+2*2^9*c.k,99800587812547+c.lower,99800968052501+c.upper)) = pointBounds19663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000301
