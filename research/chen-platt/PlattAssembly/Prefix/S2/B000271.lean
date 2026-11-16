import PlattAssemblyKernel
import PlattCertificates.Count131072.C018672
import PlattCertificates.Count131072.C018673
import PlattCertificates.Count131072.C018674
import PlattCertificates.Count131072.C018675
import PlattCertificates.Count131072.C018676
import PlattCertificates.Count131072.C018677
import PlattCertificates.Count131072.C018678
import PlattCertificates.Count131072.C018679
import PlattCertificates.Count131072.C018680
import PlattCertificates.Count131072.C018681
import PlattCertificates.Count131072.C018682
import PlattCertificates.Count131072.C018683
import PlattCertificates.Count131072.C018684
import PlattCertificates.Count131072.C018685
import PlattCertificates.Count131072.C018686
import PlattCertificates.Count131072.C018687
import PlattCertificates.Count131072.C018688
import PlattCertificates.Count131072.C018689
import PlattCertificates.Count131072.C018690
import PlattCertificates.Count131072.C018691
import PlattCertificates.Count131072.C018692
import PlattCertificates.Count131072.C018693
import PlattCertificates.Count131072.C018694
import PlattCertificates.Count131072.C018695
import PlattCertificates.Count131072.C018696
import PlattCertificates.Count131072.C018697
import PlattCertificates.Count131072.C018698
import PlattCertificates.Count131072.C018699
import PlattCertificates.Count131072.C018700
import PlattCertificates.Count131072.C018701
import PlattCertificates.Count131072.C018702
import PlattCertificates.Count131072.C018703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000271
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18672 : List PrefixCut := [⟨36,192677214,192677330⟩,
⟨111,605120822,605121186⟩,
⟨128,697781093,697781509⟩]
theorem checked18672 : checkPrefixCuts (2^48) 2451308545 9 Manual.Count131072.C018672.packed 128 cuts18672 = true := by
 decide +kernel
def pointBounds18672 : List (Nat × Nat × Nat) := [(2451345408,99129194520196,99129574359673),(2451422208,99129606963804,99129986803529)]
theorem point_links_checked18672 : (cuts18672.take 2).map (fun c => (2451308545-1+2*2^9*c.k,99129001842982+c.lower,99129381682343+c.upper)) = pointBounds18672 := by
 decide +kernel
def cuts18673 : List PrefixCut := [⟨58,310699765,310699949⟩,
⟨128,690740061,690740467⟩]
theorem checked18673 : checkPrefixCuts (2^48) 2451439617 9 Manual.Count131072.C018673.packed 128 cuts18673 = true := by
 decide +kernel
def pointBounds18673 : List (Nat × Nat × Nat) := [(2451499008,99130010323840,99130390163801)]
theorem point_links_checked18673 : (cuts18673.take 1).map (fun c => (2451439617-1+2*2^9*c.k,99129699624075+c.lower,99130079463852+c.upper)) = pointBounds18673 := by
 decide +kernel
def cuts18674 : List PrefixCut := [⟨5,27784984,27785000⟩,
⟨80,443060250,443060513⟩,
⟨128,700577094,700577512⟩]
theorem checked18674 : checkPrefixCuts (2^48) 2451570689 9 Manual.Count131072.C018674.packed 128 cuts18674 = true := by
 decide +kernel
def pointBounds18674 : List (Nat × Nat × Nat) := [(2451575808,99130418149120,99130797989319),(2451652608,99130833424386,99131213264832)]
theorem point_links_checked18674 : (cuts18674.take 2).map (fun c => (2451570689-1+2*2^9*c.k,99130390364136+c.lower,99130770204319+c.upper)) = pointBounds18674 := by
 decide +kernel
def cuts18675 : List PrefixCut := [⟨27,148331046,148331135⟩,
⟨102,568516844,568517178⟩,
⟨128,712364316,712364735⟩]
theorem checked18675 : checkPrefixCuts (2^48) 2451701761 9 Manual.Count131072.C018675.packed 128 cuts18675 = true := by
 decide +kernel
def pointBounds18675 : List (Nat × Nat × Nat) := [(2451729408,99131239272276,99131619112966),(2451806208,99131659458074,99132039299009)]
theorem point_links_checked18675 : (cuts18675.take 2).map (fun c => (2451701761-1+2*2^9*c.k,99131090941230+c.lower,99131470781831+c.upper)) = pointBounds18675 := by
 decide +kernel
def cuts18676 : List PrefixCut := [⟨49,261745461,261745621⟩,
⟨124,675705996,675706400⟩,
⟨128,697746786,697747203⟩]
theorem checked18676 : checkPrefixCuts (2^48) 2451832833 9 Manual.Count131072.C018676.packed 128 cuts18676 = true := by
 decide +kernel
def pointBounds18676 : List (Nat × Nat × Nat) := [(2451883008,99132065051007,99132444892187),(2451959808,99132479011542,99132858852966)]
theorem point_links_checked18676 : (cuts18676.take 2).map (fun c => (2451832833-1+2*2^9*c.k,99131803305546+c.lower,99132183146566+c.upper)) = pointBounds18676 := by
 decide +kernel
def cuts18677 : List PrefixCut := [⟨71,378590583,378590811⟩,
⟨128,686000677,686001094⟩]
theorem checked18677 : checkPrefixCuts (2^48) 2451963905 9 Manual.Count131072.C018677.packed 128 cuts18677 = true := by
 decide +kernel
def pointBounds18677 : List (Nat × Nat × Nat) := [(2452036608,99132879642915,99133259484580)]
theorem point_links_checked18677 : (cuts18677.take 1).map (fun c => (2451963905-1+2*2^9*c.k,99132501052332+c.lower,99132880893769+c.upper)) = pointBounds18677 := by
 decide +kernel
def cuts18678 : List PrefixCut := [⟨18,97685541,97685600⟩,
⟨93,502883301,502883604⟩,
⟨128,696983485,696983910⟩]
theorem checked18678 : checkPrefixCuts (2^48) 2452094977 9 Manual.Count131072.C018678.packed 128 cuts18678 = true := by
 decide +kernel
def pointBounds18678 : List (Nat × Nat × Nat) := [(2452113408,99133284738550,99133664580463),(2452190208,99133689936310,99134069778467)]
theorem point_links_checked18678 : (cuts18678.take 2).map (fun c => (2452094977-1+2*2^9*c.k,99133187053009+c.lower,99133566894863+c.upper)) = pointBounds18678 := by
 decide +kernel
def cuts18679 : List PrefixCut := [⟨40,216824076,216824209⟩,
⟨115,622226000,622226378⟩,
⟨128,691207341,691207761⟩]
theorem checked18679 : checkPrefixCuts (2^48) 2452226049 9 Manual.Count131072.C018679.packed 128 cuts18679 = true := by
 decide +kernel
def pointBounds18679 : List (Nat × Nat × Nat) := [(2452267008,99134100860570,99134480702982),(2452343808,99134506262494,99134886105151)]
theorem point_links_checked18679 : (cuts18679.take 2).map (fun c => (2452226049-1+2*2^9*c.k,99133884036494+c.lower,99134263878773+c.upper)) = pointBounds18679 := by
 decide +kernel
def cuts18680 : List PrefixCut := [⟨62,339965888,339966093⟩,
⟨128,706435144,706435572⟩]
theorem checked18680 : checkPrefixCuts (2^48) 2452357121 9 Manual.Count131072.C018680.packed 128 cuts18680 = true := by
 decide +kernel
def pointBounds18680 : List (Nat × Nat × Nat) := [(2452420608,99134915209723,99135295052627)]
theorem point_links_checked18680 : (cuts18680.take 1).map (fun c => (2452357121-1+2*2^9*c.k,99134575243835+c.lower,99134955086534+c.upper)) = pointBounds18680 := by
 decide +kernel
def cuts18681 : List PrefixCut := [⟨9,50040130,50040160⟩,
⟨84,469635275,469635559⟩,
⟨128,707086295,707086723⟩]
theorem checked18681 : checkPrefixCuts (2^48) 2452488193 9 Manual.Count131072.C018681.packed 128 cuts18681 = true := by
 decide +kernel
def pointBounds18681 : List (Nat × Nat × Nat) := [(2452497408,99135331719109,99135711562266),(2452574208,99135751314254,99136131157665)]
theorem point_links_checked18681 : (cuts18681.take 2).map (fun c => (2452488193-1+2*2^9*c.k,99135281678979+c.lower,99135661522106+c.upper)) = pointBounds18681 := by
 decide +kernel
def cuts18682 : List PrefixCut := [⟨31,170539710,170539813⟩,
⟨106,577370067,577370413⟩,
⟨128,698556010,698556428⟩]
theorem checked18682 : checkPrefixCuts (2^48) 2452619265 9 Manual.Count131072.C018682.packed 128 cuts18682 = true := by
 decide +kernel
def pointBounds18682 : List (Nat × Nat × Nat) := [(2452651008,99136159304984,99136539148642),(2452727808,99136566135341,99136945979242)]
theorem point_links_checked18682 : (cuts18682.take 2).map (fun c => (2452619265-1+2*2^9*c.k,99135988765274+c.lower,99136368608829+c.upper)) = pointBounds18682 := by
 decide +kernel
def cuts18683 : List PrefixCut := [⟨53,285402161,285402330⟩,
⟨128,691977422,691977839⟩]
theorem checked18683 : checkPrefixCuts (2^48) 2452750337 9 Manual.Count131072.C018683.packed 128 cuts18683 = true := by
 decide +kernel
def pointBounds18683 : List (Nat × Nat × Nat) := [(2452804608,99136972723445,99137352567587),(2452881408,99137379298706,99137759143096)]
theorem point_links_checked18683 : (cuts18683.take 2).map (fun c => (2452750337-1+2*2^9*c.k,99136687321284+c.lower,99137067165257+c.upper)) = pointBounds18683 := by
 decide +kernel
def cuts18684 : List PrefixCut := [⟨75,415168979,415169228⟩,
⟨128,707546592,707547015⟩]
theorem checked18684 : checkPrefixCuts (2^48) 2452881409 9 Manual.Count131072.C018684.packed 128 cuts18684 = true := by
 decide +kernel
def pointBounds18684 : List (Nat × Nat × Nat) := [(2452958208,99137794467685,99138174312324)]
theorem point_links_checked18684 : (cuts18684.take 1).map (fun c => (2452881409-1+2*2^9*c.k,99137379298706+c.lower,99137759143096+c.upper)) = pointBounds18684 := by
 decide +kernel
def cuts18685 : List PrefixCut := [⟨22,117729489,117729562⟩,
⟨97,527135253,527135575⟩,
⟨128,693968997,693969422⟩]
theorem checked18685 : checkPrefixCuts (2^48) 2453012481 9 Manual.Count131072.C018685.packed 128 cuts18685 = true := by
 decide +kernel
def pointBounds18685 : List (Nat × Nat × Nat) := [(2453035008,99138204574787,99138584419673),(2453111808,99138613980551,99138993825686)]
theorem point_links_checked18685 : (cuts18685.take 2).map (fun c => (2453012481-1+2*2^9*c.k,99138086845298+c.lower,99138466690111+c.upper)) = pointBounds18685 := by
 decide +kernel
def cuts18686 : List PrefixCut := [⟨44,235330553,235330696⟩,
⟨119,639776982,639777373⟩,
⟨128,689801256,689801677⟩]
theorem checked18686 : checkPrefixCuts (2^48) 2453143553 9 Manual.Count131072.C018686.packed 128 cuts18686 = true := by
 decide +kernel
def pointBounds18686 : List (Nat × Nat × Nat) := [(2453188608,99139016144848,99139395990229),(2453265408,99139420591277,99139800436906)]
theorem point_links_checked18686 : (cuts18686.take 2).map (fun c => (2453143553-1+2*2^9*c.k,99138780814295+c.lower,99139160659533+c.upper)) = pointBounds18686 := by
 decide +kernel
def cuts18687 : List PrefixCut := [⟨66,354524276,354524491⟩,
⟨128,688158334,688158752⟩]
theorem checked18687 : checkPrefixCuts (2^48) 2453274625 9 Manual.Count131072.C018687.packed 128 cuts18687 = true := by
 decide +kernel
def pointBounds18687 : List (Nat × Nat × Nat) := [(2453342208,99139825139827,99140204985701)]
theorem point_links_checked18687 : (cuts18687.take 1).map (fun c => (2453274625-1+2*2^9*c.k,99139470615551+c.lower,99139850461210+c.upper)) = pointBounds18687 := by
 decide +kernel
def cuts18688 : List PrefixCut := [⟨13,68722022,68722065⟩,
⟨88,478637313,478637603⟩,
⟨128,693857796,693858217⟩]
theorem checked18688 : checkPrefixCuts (2^48) 2453405697 9 Manual.Count131072.C018688.packed 128 cuts18688 = true := by
 decide +kernel
def pointBounds18688 : List (Nat × Nat × Nat) := [(2453419008,99140227495907,99140607342027),(2453495808,99140637411198,99141017257565)]
theorem point_links_checked18688 : (cuts18688.take 2).map (fun c => (2453405697-1+2*2^9*c.k,99140158773885+c.lower,99140538619962+c.upper)) = pointBounds18688 := by
 decide +kernel
def cuts18689 : List PrefixCut := [⟨35,186766222,186766338⟩,
⟨110,595738226,595738586⟩,
⟨128,696459235,696459655⟩]
theorem checked18689 : checkPrefixCuts (2^48) 2453536769 9 Manual.Count131072.C018689.packed 128 cuts18689 = true := by
 decide +kernel
def pointBounds18689 : List (Nat × Nat × Nat) := [(2453572608,99141039397903,99141419244517),(2453649408,99141448369907,99141828216765)]
theorem point_links_checked18689 : (cuts18689.take 2).map (fun c => (2453536769-1+2*2^9*c.k,99140852631681+c.lower,99141232478179+c.upper)) = pointBounds18689 := by
 decide +kernel
def cuts18690 : List PrefixCut := [⟨57,313744420,313744610⟩,
⟨128,700666463,700666884⟩]
theorem checked18690 : checkPrefixCuts (2^48) 2453667841 9 Manual.Count131072.C018690.packed 128 cuts18690 = true := by
 decide +kernel
def pointBounds18690 : List (Nat × Nat × Nat) := [(2453726208,99141862835336,99142242682444)]
theorem point_links_checked18690 : (cuts18690.take 1).map (fun c => (2453667841-1+2*2^9*c.k,99141549090916+c.lower,99141928937834+c.upper)) = pointBounds18690 := by
 decide +kernel
def cuts18691 : List PrefixCut := [⟨4,21336013,21336025⟩,
⟨79,431760727,431760987⟩,
⟨128,694893714,694894133⟩]
theorem checked18691 : checkPrefixCuts (2^48) 2453798913 9 Manual.Count131072.C018691.packed 128 cuts18691 = true := by
 decide +kernel
def pointBounds18691 : List (Nat × Nat × Nat) := [(2453803008,99142271093392,99142650940743),(2453879808,99142681518106,99143061365705)]
theorem point_links_checked18691 : (cuts18691.take 2).map (fun c => (2453798913-1+2*2^9*c.k,99142249757379+c.lower,99142629604718+c.upper)) = pointBounds18691 := by
 decide +kernel
def cuts18692 : List PrefixCut := [⟨26,139593671,139593755⟩,
⟨101,547354584,547354920⟩,
⟨128,689121600,689122025⟩]
theorem checked18692 : checkPrefixCuts (2^48) 2453929985 9 Manual.Count131072.C018692.packed 128 cuts18692 = true := by
 decide +kernel
def pointBounds18692 : List (Nat × Nat × Nat) := [(2453956608,99143084244764,99143464092606),(2454033408,99143492005677,99143871853771)]
theorem point_links_checked18692 : (cuts18692.take 2).map (fun c => (2453929985-1+2*2^9*c.k,99142944651093+c.lower,99143324498851+c.upper)) = pointBounds18692 := by
 decide +kernel
def cuts18693 : List PrefixCut := [⟨48,256805334,256805486⟩,
⟨123,656741531,656741919⟩,
⟨128,683349979,683350382⟩]
theorem checked18693 : checkPrefixCuts (2^48) 2454061057 9 Manual.Count131072.C018693.packed 128 cuts18693 = true := by
 decide +kernel
def pointBounds18693 : List (Nat × Nat × Nat) := [(2454110208,99143890578027,99144270426362),(2454187008,99144290514224,99144670362795)]
theorem point_links_checked18693 : (cuts18693.take 2).map (fun c => (2454061057-1+2*2^9*c.k,99143633772693+c.lower,99144013620876+c.upper)) = pointBounds18693 := by
 decide +kernel
def cuts18694 : List PrefixCut := [⟨70,381114188,381114424⟩,
⟨128,694667745,694668169⟩]
theorem checked18694 : checkPrefixCuts (2^48) 2454192129 9 Manual.Count131072.C018694.packed 128 cuts18694 = true := by
 decide +kernel
def pointBounds18694 : List (Nat × Nat × Nat) := [(2454263808,99144698236860,99145078085682)]
theorem point_links_checked18694 : (cuts18694.take 1).map (fun c => (2454192129-1+2*2^9*c.k,99144317122672+c.lower,99144696971258+c.upper)) = pointBounds18694 := by
 decide +kernel
def cuts18695 : List PrefixCut := [⟨17,92780116,92780174⟩,
⟨92,505523191,505523498⟩,
⟨128,700708663,700709091⟩]
theorem checked18695 : checkPrefixCuts (2^48) 2454323201 9 Manual.Count131072.C018695.packed 128 cuts18695 = true := by
 decide +kernel
def pointBounds18695 : List (Nat × Nat × Nat) := [(2454340608,99145104570533,99145484419601),(2454417408,99145517313608,99145897162925)]
theorem point_links_checked18695 : (cuts18695.take 2).map (fun c => (2454323201-1+2*2^9*c.k,99145011790417+c.lower,99145391639427+c.upper)) = pointBounds18695 := by
 decide +kernel
def cuts18696 : List PrefixCut := [⟨39,208599821,208599947⟩,
⟨114,619941041,619941418⟩,
⟨128,694708117,694708541⟩]
theorem checked18696 : checkPrefixCuts (2^48) 2454454273 9 Manual.Count131072.C018696.packed 128 cuts18696 = true := by
 decide +kernel
def pointBounds18696 : List (Nat × Nat × Nat) := [(2454494208,99145921098901,99146300948465),(2454571008,99146332440121,99146712289936)]
theorem point_links_checked18696 : (cuts18696.take 2).map (fun c => (2454454273-1+2*2^9*c.k,99145712499080+c.lower,99146092348518+c.upper)) = pointBounds18696 := by
 decide +kernel
def cuts18697 : List PrefixCut := [⟨61,331515658,331515862⟩,
⟨128,694212271,694212687⟩]
theorem checked18697 : checkPrefixCuts (2^48) 2454585345 9 Manual.Count131072.C018697.packed 128 cuts18697 = true := by
 decide +kernel
def pointBounds18697 : List (Nat × Nat × Nat) := [(2454647808,99146738722855,99147118572921)]
theorem point_links_checked18697 : (cuts18697.take 1).map (fun c => (2454585345-1+2*2^9*c.k,99146407207197+c.lower,99146787057059+c.upper)) = pointBounds18697 := by
 decide +kernel
def cuts18698 : List PrefixCut := [⟨8,39445372,39445396⟩,
⟨83,451091986,451092254⟩,
⟨128,695665891,695666304⟩]
theorem checked18698 : checkPrefixCuts (2^48) 2454716417 9 Manual.Count131072.C018698.packed 128 cuts18698 = true := by
 decide +kernel
def pointBounds18698 : List (Nat × Nat × Nat) := [(2454724608,99147140864840,99147520715142),(2454801408,99147552511454,99147932362000)]
theorem point_links_checked18698 : (cuts18698.take 2).map (fun c => (2454716417-1+2*2^9*c.k,99147101419468+c.lower,99147481269746+c.upper)) = pointBounds18698 := by
 decide +kernel
def cuts18699 : List PrefixCut := [⟨30,159033599,159033695⟩,
⟨105,571342359,571342696⟩,
⟨128,694826104,694826517⟩]
theorem checked18699 : checkPrefixCuts (2^48) 2454847489 9 Manual.Count131072.C018699.packed 128 cuts18699 = true := by
 decide +kernel
def pointBounds18699 : List (Nat × Nat × Nat) := [(2454878208,99147956118958,99148335969745),(2454955008,99148368427718,99148748278746)]
theorem point_links_checked18699 : (cuts18699.take 2).map (fun c => (2454847489-1+2*2^9*c.k,99147797085359+c.lower,99148176936050+c.upper)) = pointBounds18699 := by
 decide +kernel
def cuts18700 : List PrefixCut := [⟨52,283079447,283079613⟩,
⟨127,694101300,694101707⟩,
⟨128,699833731,699834142⟩]
theorem checked18700 : checkPrefixCuts (2^48) 2454978561 9 Manual.Count131072.C018700.packed 128 cuts18700 = true := by
 decide +kernel
def pointBounds18700 : List (Nat × Nat × Nat) := [(2455031808,99148774990910,99149154842180),(2455108608,99149186012763,99149565864274)]
theorem point_links_checked18700 : (cuts18700.take 2).map (fun c => (2454978561-1+2*2^9*c.k,99148491911463+c.lower,99148871762567+c.upper)) = pointBounds18700 := by
 decide +kernel
def cuts18701 : List PrefixCut := [⟨74,406766933,406767174⟩,
⟨128,706216467,706216889⟩]
theorem checked18701 : checkPrefixCuts (2^48) 2455109633 9 Manual.Count131072.C018701.packed 128 cuts18701 = true := by
 decide +kernel
def pointBounds18701 : List (Nat × Nat × Nat) := [(2455185408,99149598512127,99149978363883)]
theorem point_links_checked18701 : (cuts18701.take 1).map (fun c => (2455109633-1+2*2^9*c.k,99149191745194+c.lower,99149571596709+c.upper)) = pointBounds18701 := by
 decide +kernel
def cuts18702 : List PrefixCut := [⟨21,114412693,114412762⟩,
⟨96,526771623,526771937⟩,
⟨128,701707873,701708295⟩]
theorem checked18702 : checkPrefixCuts (2^48) 2455240705 9 Manual.Count131072.C018702.packed 128 cuts18702 = true := by
 decide +kernel
def pointBounds18702 : List (Nat × Nat × Nat) := [(2455262208,99150012374354,99150392226360),(2455339008,99150424733284,99150804585535)]
theorem point_links_checked18702 : (cuts18702.take 2).map (fun c => (2455240705-1+2*2^9*c.k,99149897961661+c.lower,99150277813598+c.upper)) = pointBounds18702 := by
 decide +kernel
def cuts18703 : List PrefixCut := [⟨43,229614577,229614717⟩,
⟨118,639998923,639999310⟩,
⟨128,692728947,692729366⟩]
theorem checked18703 : checkPrefixCuts (2^48) 2455371777 9 Manual.Count131072.C018703.packed 128 cuts18703 = true := by
 decide +kernel
def pointBounds18703 : List (Nat × Nat × Nat) := [(2455415808,99150829284111,99151209136610),(2455492608,99151239668457,99151619521203)]
theorem point_links_checked18703 : (cuts18703.take 2).map (fun c => (2455371777-1+2*2^9*c.k,99150599669534+c.lower,99150979521893+c.upper)) = pointBounds18703 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000271
