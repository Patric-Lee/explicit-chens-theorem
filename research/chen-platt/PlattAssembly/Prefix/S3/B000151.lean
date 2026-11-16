import PlattAssemblyKernel
import PlattCertificates.Count131072.C024832
import PlattCertificates.Count131072.C024833
import PlattCertificates.Count131072.C024834
import PlattCertificates.Count131072.C024835
import PlattCertificates.Count131072.C024836
import PlattCertificates.Count131072.C024837
import PlattCertificates.Count131072.C024838
import PlattCertificates.Count131072.C024839
import PlattCertificates.Count131072.C024840
import PlattCertificates.Count131072.C024841
import PlattCertificates.Count131072.C024842
import PlattCertificates.Count131072.C024843
import PlattCertificates.Count131072.C024844
import PlattCertificates.Count131072.C024845
import PlattCertificates.Count131072.C024846
import PlattCertificates.Count131072.C024847
import PlattCertificates.Count131072.C024848
import PlattCertificates.Count131072.C024849
import PlattCertificates.Count131072.C024850
import PlattCertificates.Count131072.C024851
import PlattCertificates.Count131072.C024852
import PlattCertificates.Count131072.C024853
import PlattCertificates.Count131072.C024854
import PlattCertificates.Count131072.C024855
import PlattCertificates.Count131072.C024856
import PlattCertificates.Count131072.C024857
import PlattCertificates.Count131072.C024858
import PlattCertificates.Count131072.C024859
import PlattCertificates.Count131072.C024860
import PlattCertificates.Count131072.C024861
import PlattCertificates.Count131072.C024862
import PlattCertificates.Count131072.C024863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000151
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24832 : List PrefixCut := [⟨27,109438084,109438147⟩,
⟨127,510127167,510127456⟩,
⟨128,514013937,514014228⟩]
theorem checked24832 : checkPrefixCuts (2^48) 3258712065 9 Manual.Count131072.C024832.packed 128 cuts24832 = true := by
 decide +kernel
def pointBounds24832 : List (Nat × Nat × Nat) := [(3258739712,102811640857346,102812022825301),(3258842112,102812041546429,102812423514610)]
theorem point_links_checked24832 : (cuts24832.take 2).map (fun c => (3258712065-1+2*2^9*c.k,102811531419262+c.lower,102811913387154+c.upper)) = pointBounds24832 := by
 decide +kernel
def cuts24833 : List PrefixCut := [⟨99,396012462,396012683⟩,
⟨128,513475069,513475356⟩]
theorem checked24833 : checkPrefixCuts (2^48) 3258843137 9 Manual.Count131072.C024833.packed 128 cuts24833 = true := by
 decide +kernel
def pointBounds24833 : List (Nat × Nat × Nat) := [(3258944512,102812441445661,102812823414065)]
theorem point_links_checked24833 : (cuts24833.take 1).map (fun c => (3258843137-1+2*2^9*c.k,102812045433199+c.lower,102812427401382+c.upper)) = pointBounds24833 := by
 decide +kernel
def cuts24834 : List PrefixCut := [⟨71,287260631,287260794⟩,
⟨128,524250196,524250491⟩]
theorem checked24834 : checkPrefixCuts (2^48) 3258974209 9 Manual.Count131072.C024834.packed 128 cuts24834 = true := by
 decide +kernel
def pointBounds24834 : List (Nat × Nat × Nat) := [(3259046912,102812846168899,102813228137532)]
theorem point_links_checked24834 : (cuts24834.take 1).map (fun c => (3258974209-1+2*2^9*c.k,102812558908268+c.lower,102812940876738+c.upper)) = pointBounds24834 := by
 decide +kernel
def cuts24835 : List PrefixCut := [⟨43,171866601,171866695⟩,
⟨128,519133777,519134054⟩]
theorem checked24835 : checkPrefixCuts (2^48) 3259105281 9 Manual.Count131072.C024835.packed 128 cuts24835 = true := by
 decide +kernel
def pointBounds24835 : List (Nat × Nat × Nat) := [(3259149312,102813255025065,102813636993924)]
theorem point_links_checked24835 : (cuts24835.take 1).map (fun c => (3259105281-1+2*2^9*c.k,102813083158464+c.lower,102813465127229+c.upper)) = pointBounds24835 := by
 decide +kernel
def cuts24836 : List PrefixCut := [⟨15,60626141,60626177⟩,
⟨115,464965841,464966107⟩,
⟨128,514967659,514967953⟩]
theorem checked24836 : checkPrefixCuts (2^48) 3259236353 9 Manual.Count131072.C024836.packed 128 cuts24836 = true := by
 decide +kernel
def pointBounds24836 : List (Nat × Nat × Nat) := [(3259251712,102813662918382,102814044887460),(3259354112,102814067258082,102814449227390)]
theorem point_links_checked24836 : (cuts24836.take 2).map (fun c => (3259236353-1+2*2^9*c.k,102813602292241+c.lower,102813984261283+c.upper)) = pointBounds24836 := by
 decide +kernel
def cuts24837 : List PrefixCut := [⟨87,357433955,357434158⟩,
⟨128,524014368,524014663⟩]
theorem checked24837 : checkPrefixCuts (2^48) 3259367425 9 Manual.Count131072.C024837.packed 128 cuts24837 = true := by
 decide +kernel
def pointBounds24837 : List (Nat × Nat × Nat) := [(3259456512,102814474693855,102814856663394)]
theorem point_links_checked24837 : (cuts24837.take 1).map (fun c => (3259367425-1+2*2^9*c.k,102814117259900+c.lower,102814499229236+c.upper)) = pointBounds24837 := by
 decide +kernel
def cuts24838 : List PrefixCut := [⟨59,243087860,243087993⟩,
⟨128,519848370,519848660⟩]
theorem checked24838 : checkPrefixCuts (2^48) 3259498497 9 Manual.Count131072.C024838.packed 128 cuts24838 = true := by
 decide +kernel
def pointBounds24838 : List (Nat × Nat × Nat) := [(3259558912,102814884362128,102815266331892)]
theorem point_links_checked24838 : (cuts24838.take 1).map (fun c => (3259498497-1+2*2^9*c.k,102814641274268+c.lower,102815023243899+c.upper)) = pointBounds24838 := by
 decide +kernel
def cuts24839 : List PrefixCut := [⟨31,127800049,127800118⟩,
⟨128,517064270,517064560⟩]
theorem checked24839 : checkPrefixCuts (2^48) 3259629569 9 Manual.Count131072.C024839.packed 128 cuts24839 = true := by
 decide +kernel
def pointBounds24839 : List (Nat × Nat × Nat) := [(3259661312,102815288922687,102815670892677)]
theorem point_links_checked24839 : (cuts24839.take 1).map (fun c => (3259629569-1+2*2^9*c.k,102815161122638+c.lower,102815543092559+c.upper)) = pointBounds24839 := by
 decide +kernel
def cuts24840 : List PrefixCut := [⟨3,12693199,12693206⟩,
⟨103,416623983,416624227⟩,
⟨128,516525367,516525670⟩]
theorem checked24840 : checkPrefixCuts (2^48) 3259760641 9 Manual.Count131072.C024840.packed 128 cuts24840 = true := by
 decide +kernel
def pointBounds24840 : List (Nat × Nat × Nat) := [(3259763712,102815690880107,102816072850325),(3259866112,102816094810891,102816476781346)]
theorem point_links_checked24840 : (cuts24840.take 2).map (fun c => (3259760641-1+2*2^9*c.k,102815678186908+c.lower,102816060157119+c.upper)) = pointBounds24840 := by
 decide +kernel
def cuts24841 : List PrefixCut := [⟨75,304793779,304793947⟩,
⟨128,518835871,518836158⟩]
theorem checked24841 : checkPrefixCuts (2^48) 3259891713 9 Manual.Count131072.C024841.packed 128 cuts24841 = true := by
 decide +kernel
def pointBounds24841 : List (Nat × Nat × Nat) := [(3259968512,102816499506054,102816881476736)]
theorem point_links_checked24841 : (cuts24841.take 1).map (fun c => (3259891713-1+2*2^9*c.k,102816194712275+c.lower,102816576682789+c.upper)) = pointBounds24841 := by
 decide +kernel
def cuts24842 : List PrefixCut := [⟨47,192539865,192539974⟩,
⟨128,513893660,513893953⟩]
theorem checked24842 : checkPrefixCuts (2^48) 3260022785 9 Manual.Count131072.C024842.packed 128 cuts24842 = true := by
 decide +kernel
def pointBounds24842 : List (Nat × Nat × Nat) := [(3260070912,102816906088011,102817288058921)]
theorem point_links_checked24842 : (cuts24842.take 1).map (fun c => (3260022785-1+2*2^9*c.k,102816713548146+c.lower,102817095518947+c.upper)) = pointBounds24842 := by
 decide +kernel
def cuts24843 : List PrefixCut := [⟨19,77013189,77013235⟩,
⟨119,481324887,481325164⟩,
⟨128,517758074,517758373⟩]
theorem checked24843 : checkPrefixCuts (2^48) 3260153857 9 Manual.Count131072.C024843.packed 128 cuts24843 = true := by
 decide +kernel
def pointBounds24843 : List (Nat × Nat × Nat) := [(3260173312,102817304454995,102817686426135),(3260275712,102817708766693,102818090738064)]
theorem point_links_checked24843 : (cuts24843.take 2).map (fun c => (3260153857-1+2*2^9*c.k,102817227441806+c.lower,102817609412900+c.upper)) = pointBounds24843 := by
 decide +kernel
def cuts24844 : List PrefixCut := [⟨91,369937883,369938090⟩,
⟨128,518169025,518169320⟩]
theorem checked24844 : checkPrefixCuts (2^48) 3260284929 9 Manual.Count131072.C024844.packed 128 cuts24844 = true := by
 decide +kernel
def pointBounds24844 : List (Nat × Nat × Nat) := [(3260378112,102818115137763,102818497109363)]
theorem point_links_checked24844 : (cuts24844.take 1).map (fun c => (3260284929-1+2*2^9*c.k,102817745199880+c.lower,102818127171273+c.upper)) = pointBounds24844 := by
 decide +kernel
def cuts24845 : List PrefixCut := [⟨63,255709787,255709929⟩,
⟨128,515040244,515040537⟩]
theorem checked24845 : checkPrefixCuts (2^48) 3260416001 9 Manual.Count131072.C024845.packed 128 cuts24845 = true := by
 decide +kernel
def pointBounds24845 : List (Nat × Nat × Nat) := [(3260480512,102818519078692,102818901050522)]
theorem point_links_checked24845 : (cuts24845.take 1).map (fun c => (3260416001-1+2*2^9*c.k,102818263368905+c.lower,102818645340593+c.upper)) = pointBounds24845 := by
 decide +kernel
def cuts24846 : List PrefixCut := [⟨35,141662656,141662737⟩,
⟨128,512170884,512171177⟩]
theorem checked24846 : checkPrefixCuts (2^48) 3260547073 9 Manual.Count131072.C024846.packed 128 cuts24846 = true := by
 decide +kernel
def pointBounds24846 : List (Nat × Nat × Nat) := [(3260582912,102818920071805,102819302043867)]
theorem point_links_checked24846 : (cuts24846.take 1).map (fun c => (3260547073-1+2*2^9*c.k,102818778409149+c.lower,102819160381130+c.upper)) = pointBounds24846 := by
 decide +kernel
def cuts24847 : List PrefixCut := [⟨7,28918521,28918538⟩,
⟨107,436706002,436706239⟩,
⟨128,523113168,523113458⟩]
theorem checked24847 : checkPrefixCuts (2^48) 3260678145 9 Manual.Count131072.C024847.packed 128 cuts24847 = true := by
 decide +kernel
def pointBounds24847 : List (Nat × Nat × Nat) := [(3260685312,102819319498554,102819701470845),(3260787712,102819727286035,102820109258546)]
theorem point_links_checked24847 : (cuts24847.take 2).map (fun c => (3260678145-1+2*2^9*c.k,102819290580033+c.lower,102819672552307+c.upper)) = pointBounds24847 := by
 decide +kernel
def cuts24848 : List PrefixCut := [⟨79,316533556,316533733⟩,
⟨128,512474864,512475154⟩]
theorem checked24848 : checkPrefixCuts (2^48) 3260809217 9 Manual.Count131072.C024848.packed 128 cuts24848 = true := by
 decide +kernel
def pointBounds24848 : List (Nat × Nat × Nat) := [(3260890112,102820130226757,102820512199498)]
theorem point_links_checked24848 : (cuts24848.take 1).map (fun c => (3260809217-1+2*2^9*c.k,102819813693201+c.lower,102820195665765+c.upper)) = pointBounds24848 := by
 decide +kernel
def cuts24849 : List PrefixCut := [⟨51,208885707,208885822⟩,
⟨128,515216494,515216783⟩]
theorem checked24849 : checkPrefixCuts (2^48) 3260940289 9 Manual.Count131072.C024849.packed 128 cuts24849 = true := by
 decide +kernel
def pointBounds24849 : List (Nat × Nat × Nat) := [(3260992512,102820535053772,102820917026741)]
theorem point_links_checked24849 : (cuts24849.take 1).map (fun c => (3260940289-1+2*2^9*c.k,102820326168065+c.lower,102820708140919+c.upper)) = pointBounds24849 := by
 decide +kernel
def cuts24850 : List PrefixCut := [⟨23,91751047,91751101⟩,
⟨123,496380010,496380294⟩,
⟨128,516576602,516576899⟩]
theorem checked24850 : checkPrefixCuts (2^48) 3261071361 9 Manual.Count131072.C024850.packed 128 cuts24850 = true := by
 decide +kernel
def pointBounds24850 : List (Nat × Nat × Nat) := [(3261094912,102820933135606,102821315108803),(3261197312,102821337764569,102821719737996)]
theorem point_links_checked24850 : (cuts24850.take 2).map (fun c => (3261071361-1+2*2^9*c.k,102820841384559+c.lower,102821223357702+c.upper)) = pointBounds24850 := by
 decide +kernel
def cuts24851 : List PrefixCut := [⟨95,380967295,380967512⟩,
⟨128,513276119,513276410⟩]
theorem checked24851 : checkPrefixCuts (2^48) 3261202433 9 Manual.Count131072.C024851.packed 128 cuts24851 = true := by
 decide +kernel
def pointBounds24851 : List (Nat × Nat × Nat) := [(3261299712,102821738928456,102822120902113)]
theorem point_links_checked24851 : (cuts24851.take 1).map (fun c => (3261202433-1+2*2^9*c.k,102821357961161+c.lower,102821739934601+c.upper)) = pointBounds24851 := by
 decide +kernel
def cuts24852 : List PrefixCut := [⟨67,275746995,275747146⟩,
⟨128,516103747,516104035⟩]
theorem checked24852 : checkPrefixCuts (2^48) 3261333505 9 Manual.Count131072.C024852.packed 128 cuts24852 = true := by
 decide +kernel
def pointBounds24852 : List (Nat × Nat × Nat) := [(3261402112,102822146984275,102822528958157)]
theorem point_links_checked24852 : (cuts24852.take 1).map (fun c => (3261333505-1+2*2^9*c.k,102821871237280+c.lower,102822253211011+c.upper)) = pointBounds24852 := by
 decide +kernel
def cuts24853 : List PrefixCut := [⟨39,158710647,158710735⟩,
⟨128,509437716,509438004⟩]
theorem checked24853 : checkPrefixCuts (2^48) 3261464577 9 Manual.Count131072.C024853.packed 128 cuts24853 = true := by
 decide +kernel
def pointBounds24853 : List (Nat × Nat × Nat) := [(3261504512,102822546051674,102822928025781)]
theorem point_links_checked24853 : (cuts24853.take 1).map (fun c => (3261464577-1+2*2^9*c.k,102822387341027+c.lower,102822769315046+c.upper)) = pointBounds24853 := by
 decide +kernel
def cuts24854 : List PrefixCut := [⟨11,43926497,43926523⟩,
⟨111,447887871,447888122⟩,
⟨128,519600273,519600562⟩]
theorem checked24854 : checkPrefixCuts (2^48) 3261595649 9 Manual.Count131072.C024854.packed 128 cuts24854 = true := by
 decide +kernel
def pointBounds24854 : List (Nat × Nat × Nat) := [(3261606912,102822940705240,102823322679573),(3261709312,102823344666614,102823726641172)]
theorem point_links_checked24854 : (cuts24854.take 2).map (fun c => (3261595649-1+2*2^9*c.k,102822896778743+c.lower,102823278753050+c.upper)) = pointBounds24854 := by
 decide +kernel
def cuts24855 : List PrefixCut := [⟨83,334134993,334135179⟩,
⟨128,513107545,513107832⟩]
theorem checked24855 : checkPrefixCuts (2^48) 3261726721 9 Manual.Count131072.C024855.packed 128 cuts24855 = true := by
 decide +kernel
def pointBounds24855 : List (Nat × Nat × Nat) := [(3261811712,102823750514009,102824132488791)]
theorem point_links_checked24855 : (cuts24855.take 1).map (fun c => (3261726721-1+2*2^9*c.k,102823416379016+c.lower,102823798353612+c.upper)) = pointBounds24855 := by
 decide +kernel
def cuts24856 : List PrefixCut := [⟨55,223496465,223496588⟩,
⟨128,519731207,519731500⟩]
theorem checked24856 : checkPrefixCuts (2^48) 3261857793 9 Manual.Count131072.C024856.packed 128 cuts24856 = true := by
 decide +kernel
def pointBounds24856 : List (Nat × Nat × Nat) := [(3261914112,102824152983026,102824534958032)]
theorem point_links_checked24856 : (cuts24856.take 1).map (fun c => (3261857793-1+2*2^9*c.k,102823929486561+c.lower,102824311461444+c.upper)) = pointBounds24856 := by
 decide +kernel
def cuts24857 : List PrefixCut := [⟨27,108724112,108724170⟩,
⟨127,512462168,512462453⟩,
⟨128,515654746,515655033⟩]
theorem checked24857 : checkPrefixCuts (2^48) 3261988865 9 Manual.Count131072.C024857.packed 128 cuts24857 = true := by
 decide +kernel
def pointBounds24857 : List (Nat × Nat × Nat) := [(3262016512,102824557941880,102824939917114),(3262118912,102824961679936,102825343655397)]
theorem point_links_checked24857 : (cuts24857.take 2).map (fun c => (3261988865-1+2*2^9*c.k,102824449217768+c.lower,102824831192944+c.upper)) = pointBounds24857 := by
 decide +kernel
def cuts24858 : List PrefixCut := [⟨99,395787144,395787362⟩,
⟨128,510543280,510543564⟩]
theorem checked24858 : checkPrefixCuts (2^48) 3262119937 9 Manual.Count131072.C024858.packed 128 cuts24858 = true := by
 decide +kernel
def pointBounds24858 : List (Nat × Nat × Nat) := [(3262221312,102825360659658,102825742635339)]
theorem point_links_checked24858 : (cuts24858.take 1).map (fun c => (3262119937-1+2*2^9*c.k,102824964872514+c.lower,102825346847977+c.upper)) = pointBounds24858 := by
 decide +kernel
def cuts24859 : List PrefixCut := [⟨71,283607137,283607293⟩,
⟨128,512938672,512938957⟩]
theorem checked24859 : checkPrefixCuts (2^48) 3262251009 9 Manual.Count131072.C024859.packed 128 cuts24859 = true := by
 decide +kernel
def pointBounds24859 : List (Nat × Nat × Nat) := [(3262323712,102825759022931,102826140998834)]
theorem point_links_checked24859 : (cuts24859.take 1).map (fun c => (3262251009-1+2*2^9*c.k,102825475415794+c.lower,102825857391541+c.upper)) = pointBounds24859 := by
 decide +kernel
def cuts24860 : List PrefixCut := [⟨43,174109752,174109849⟩,
⟨128,513435744,513436029⟩]
theorem checked24860 : checkPrefixCuts (2^48) 3262382081 9 Manual.Count131072.C024860.packed 128 cuts24860 = true := by
 decide +kernel
def pointBounds24860 : List (Nat × Nat × Nat) := [(3262426112,102826162464218,102826544440347)]
theorem point_links_checked24860 : (cuts24860.take 1).map (fun c => (3262382081-1+2*2^9*c.k,102825988354466+c.lower,102826370330498+c.upper)) = pointBounds24860 := by
 decide +kernel
def cuts24861 : List PrefixCut := [⟨15,58494642,58494672⟩,
⟨115,464153678,464153933⟩,
⟨128,517469891,517470175⟩]
theorem checked24861 : checkPrefixCuts (2^48) 3262513153 9 Manual.Count131072.C024861.packed 128 cuts24861 = true := by
 decide +kernel
def pointBounds24861 : List (Nat × Nat × Nat) := [(3262528512,102826560284852,102826942261199),(3262630912,102826965943888,102827347920460)]
theorem point_links_checked24861 : (cuts24861.take 2).map (fun c => (3262513153-1+2*2^9*c.k,102826501790210+c.lower,102826883766527+c.upper)) = pointBounds24861 := by
 decide +kernel
def cuts24862 : List PrefixCut := [⟨87,353020231,353020424⟩,
⟨128,520986167,520986453⟩]
theorem checked24862 : checkPrefixCuts (2^48) 3262644225 9 Manual.Count131072.C024862.packed 128 cuts24862 = true := by
 decide +kernel
def pointBounds24862 : List (Nat × Nat × Nat) := [(3262733312,102827372280332,102827754257126)]
theorem point_links_checked24862 : (cuts24862.take 1).map (fun c => (3262644225-1+2*2^9*c.k,102827019260101+c.lower,102827401236702+c.upper)) = pointBounds24862 := by
 decide +kernel
def cuts24863 : List PrefixCut := [⟨59,235942316,235942454⟩,
⟨128,509750668,509750966⟩]
theorem checked24863 : checkPrefixCuts (2^48) 3262775297 9 Manual.Count131072.C024863.packed 128 cuts24863 = true := by
 decide +kernel
def pointBounds24863 : List (Nat × Nat × Nat) := [(3262835712,102827776188584,102828158165609)]
theorem point_links_checked24863 : (cuts24863.take 1).map (fun c => (3262775297-1+2*2^9*c.k,102827540246268+c.lower,102827922223155+c.upper)) = pointBounds24863 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000151
