import PlattAssemblyKernel
import PlattCertificates.Count131072.C016688
import PlattCertificates.Count131072.C016689
import PlattCertificates.Count131072.C016690
import PlattCertificates.Count131072.C016691
import PlattCertificates.Count131072.C016692
import PlattCertificates.Count131072.C016693
import PlattCertificates.Count131072.C016694
import PlattCertificates.Count131072.C016695
import PlattCertificates.Count131072.C016696
import PlattCertificates.Count131072.C016697
import PlattCertificates.Count131072.C016698
import PlattCertificates.Count131072.C016699
import PlattCertificates.Count131072.C016700
import PlattCertificates.Count131072.C016701
import PlattCertificates.Count131072.C016702
import PlattCertificates.Count131072.C016703
import PlattCertificates.Count131072.C016704
import PlattCertificates.Count131072.C016705
import PlattCertificates.Count131072.C016706
import PlattCertificates.Count131072.C016707
import PlattCertificates.Count131072.C016708
import PlattCertificates.Count131072.C016709
import PlattCertificates.Count131072.C016710
import PlattCertificates.Count131072.C016711
import PlattCertificates.Count131072.C016712
import PlattCertificates.Count131072.C016713
import PlattCertificates.Count131072.C016714
import PlattCertificates.Count131072.C016715
import PlattCertificates.Count131072.C016716
import PlattCertificates.Count131072.C016717
import PlattCertificates.Count131072.C016718
import PlattCertificates.Count131072.C016719
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000209
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16688 : List PrefixCut := [⟨61,374050874,374051105⟩,
⟨128,785340375,785340862⟩]
theorem checked16688 : checkPrefixCuts (2^48) 2191261697 9 Manual.Count131072.C016688.packed 128 cuts16688 = true := by
 decide +kernel
def pointBounds16688 : List (Nat × Nat × Nat) := [(2191324160,97665590619455,97665969558076),(2191392768,97666001908956,97666380847833)]
theorem point_links_checked16688 : (cuts16688.take 2).map (fun c => (2191261697-1+2*2^9*c.k,97665216568581+c.lower,97665595506971+c.upper)) = pointBounds16688 := by
 decide +kernel
def cuts16689 : List PrefixCut := [⟨67,413331674,413331932⟩,
⟨128,783623674,783624165⟩]
theorem checked16689 : checkPrefixCuts (2^48) 2191392769 9 Manual.Count131072.C016689.packed 128 cuts16689 = true := by
 decide +kernel
def pointBounds16689 : List (Nat × Nat × Nat) := [(2191461376,97666415240630,97666794179765)]
theorem point_links_checked16689 : (cuts16689.take 1).map (fun c => (2191392769-1+2*2^9*c.k,97666001908956+c.lower,97666380847833+c.upper)) = pointBounds16689 := by
 decide +kernel
def cuts16690 : List PrefixCut := [⟨6,35320393,35320416⟩,
⟨73,440277779,440278059⟩,
⟨128,776255743,776256234⟩]
theorem checked16690 : checkPrefixCuts (2^48) 2191523841 9 Manual.Count131072.C016690.packed 128 cuts16690 = true := by
 decide +kernel
def pointBounds16690 : List (Nat × Nat × Nat) := [(2191529984,97666820853023,97667199792414),(2191598592,97667225810409,97667604750057)]
theorem point_links_checked16690 : (cuts16690.take 2).map (fun c => (2191523841-1+2*2^9*c.k,97666785532630+c.lower,97667164471998+c.upper)) = pointBounds16690 := by
 decide +kernel
def cuts16691 : List PrefixCut := [⟨12,72819778,72819821⟩,
⟨79,479036120,479036414⟩,
⟨128,779291595,779292078⟩]
theorem checked16691 : checkPrefixCuts (2^48) 2191654913 9 Manual.Count131072.C016691.packed 128 cuts16691 = true := by
 decide +kernel
def pointBounds16691 : List (Nat × Nat × Nat) := [(2191667200,97667634608151,97668013548053),(2191735808,97668040824493,97668419764646)]
theorem point_links_checked16691 : (cuts16691.take 2).map (fun c => (2191654913-1+2*2^9*c.k,97667561788373+c.lower,97667940728232+c.upper)) = pointBounds16691 := by
 decide +kernel
def cuts16692 : List PrefixCut := [⟨18,106590312,106590382⟩,
⟨85,520486406,520486742⟩,
⟨128,793114057,793114561⟩]
theorem checked16692 : checkPrefixCuts (2^48) 2191785985 9 Manual.Count131072.C016692.packed 128 cuts16692 = true := by
 decide +kernel
def pointBounds16692 : List (Nat × Nat × Nat) := [(2191804416,97668447670280,97668826610692),(2191873024,97668861566374,97669240507052)]
theorem point_links_checked16692 : (cuts16692.take 2).map (fun c => (2191785985-1+2*2^9*c.k,97668341079968+c.lower,97668720020310+c.upper)) = pointBounds16692 := by
 decide +kernel
def cuts16693 : List PrefixCut := [⟨24,144080735,144080830⟩,
⟨91,553841783,553842134⟩,
⟨128,780610946,780611437⟩]
theorem checked16693 : checkPrefixCuts (2^48) 2191917057 9 Manual.Count131072.C016693.packed 128 cuts16693 = true := by
 decide +kernel
def pointBounds16693 : List (Nat × Nat × Nat) := [(2191941632,97669278274760,97669657215701),(2192010240,97669688035808,97670066977005)]
theorem point_links_checked16693 : (cuts16693.take 2).map (fun c => (2191917057-1+2*2^9*c.k,97669134194025+c.lower,97669513134871+c.upper)) = pointBounds16693 := by
 decide +kernel
def cuts16694 : List PrefixCut := [⟨30,183107478,183107593⟩,
⟨97,587706722,587707091⟩,
⟨128,774657879,774658367⟩]
theorem checked16694 : checkPrefixCuts (2^48) 2192048129 9 Manual.Count131072.C016694.packed 128 cuts16694 = true := by
 decide +kernel
def pointBounds16694 : List (Nat × Nat × Nat) := [(2192078848,97670097912449,97670476853901),(2192147456,97670502511693,97670881453399)]
theorem point_links_checked16694 : (cuts16694.take 2).map (fun c => (2192048129-1+2*2^9*c.k,97669914804971+c.lower,97670293746308+c.upper)) = pointBounds16694 := by
 decide +kernel
def cuts16695 : List PrefixCut := [⟨36,224954159,224954299⟩,
⟨103,636204639,636205040⟩,
⟨128,788093121,788093618⟩]
theorem checked16695 : checkPrefixCuts (2^48) 2192179201 9 Manual.Count131072.C016695.packed 128 cuts16695 = true := by
 decide +kernel
def pointBounds16695 : List (Nat × Nat × Nat) := [(2192216064,97670914417009,97671293358974),(2192284672,97671325667489,97671704609715)]
theorem point_links_checked16695 : (cuts16695.take 2).map (fun c => (2192179201-1+2*2^9*c.k,97670689462850+c.lower,97671068404675+c.upper)) = pointBounds16695 := by
 decide +kernel
def cuts16696 : List PrefixCut := [⟨42,256524480,256524642⟩,
⟨109,663512440,663512858⟩,
⟨128,780214223,780214717⟩]
theorem checked16696 : checkPrefixCuts (2^48) 2192310273 9 Manual.Count131072.C016696.packed 128 cuts16696 = true := by
 decide +kernel
def pointBounds16696 : List (Nat × Nat × Nat) := [(2192353280,97671734080451,97672113022935),(2192421888,97672141068411,97672520011151)]
theorem point_links_checked16696 : (cuts16696.take 2).map (fun c => (2192310273-1+2*2^9*c.k,97671477555971+c.lower,97671856498293+c.upper)) = pointBounds16696 := by
 decide +kernel
def cuts16697 : List PrefixCut := [⟨48,292584367,292584554⟩,
⟨115,702371187,702371631⟩,
⟨128,782863524,782864017⟩]
theorem checked16697 : checkPrefixCuts (2^48) 2192441345 9 Manual.Count131072.C016697.packed 128 cuts16697 = true := by
 decide +kernel
def pointBounds16697 : List (Nat × Nat × Nat) := [(2192490496,97672550354561,97672929297564),(2192559104,97672960141381,97673339084641)]
theorem point_links_checked16697 : (cuts16697.take 2).map (fun c => (2192441345-1+2*2^9*c.k,97672257770194+c.lower,97672636713010+c.upper)) = pointBounds16697 := by
 decide +kernel
def cuts16698 : List PrefixCut := [⟨54,333774841,333775050⟩,
⟨121,751751818,751752293⟩,
⟨128,794241983,794242487⟩]
theorem checked16698 : checkPrefixCuts (2^48) 2192572417 9 Manual.Count131072.C016698.packed 128 cuts16698 = true := by
 decide +kernel
def pointBounds16698 : List (Nat × Nat × Nat) := [(2192627712,97673374408559,97673753352077),(2192696320,97673792385536,97674171329320)]
theorem point_links_checked16698 : (cuts16698.take 2).map (fun c => (2192572417-1+2*2^9*c.k,97673040633718+c.lower,97673419577027+c.upper)) = pointBounds16698 := by
 decide +kernel
def cuts16699 : List PrefixCut := [⟨60,366488082,366488310⟩,
⟨127,776352008,776352494⟩,
⟨128,782770070,782770560⟩]
theorem checked16699 : checkPrefixCuts (2^48) 2192703489 9 Manual.Count131072.C016699.packed 128 cuts16699 = true := by
 decide +kernel
def pointBounds16699 : List (Nat × Nat × Nat) := [(2192764928,97674201363783,97674580307824),(2192833536,97674611227709,97674990172008)]
theorem point_links_checked16699 : (cuts16699.take 2).map (fun c => (2192703489-1+2*2^9*c.k,97673834875701+c.lower,97674213819514+c.upper)) = pointBounds16699 := by
 decide +kernel
def cuts16700 : List PrefixCut := [⟨66,406256913,406257167⟩,
⟨128,781568052,781568543⟩]
theorem checked16700 : checkPrefixCuts (2^48) 2192834561 9 Manual.Count131072.C016700.packed 128 cuts16700 = true := by
 decide +kernel
def pointBounds16700 : List (Nat × Nat × Nat) := [(2192902144,97675023902684,97675402847241)]
theorem point_links_checked16700 : (cuts16700.take 1).map (fun c => (2192834561-1+2*2^9*c.k,97674617645771+c.lower,97674996590074+c.upper)) = pointBounds16700 := by
 decide +kernel
def cuts16701 : List PrefixCut := [⟨5,30163043,30163062⟩,
⟨72,446534392,446534670⟩,
⟨128,783446695,783447186⟩]
theorem checked16701 : checkPrefixCuts (2^48) 2192965633 9 Manual.Count131072.C016701.packed 128 cuts16701 = true := by
 decide +kernel
def pointBounds16701 : List (Nat × Nat × Nat) := [(2192970752,97675429376866,97675808321679),(2193039360,97675845748215,97676224693287)]
theorem point_links_checked16701 : (cuts16701.take 2).map (fun c => (2192965633-1+2*2^9*c.k,97675399213823+c.lower,97675778158617+c.upper)) = pointBounds16701 := by
 decide +kernel
def cuts16702 : List PrefixCut := [⟨11,63146010,63146051⟩,
⟨78,476026103,476026410⟩,
⟨128,781474501,781475006⟩]
theorem checked16702 : checkPrefixCuts (2^48) 2193096705 9 Manual.Count131072.C016702.packed 128 cuts16702 = true := by
 decide +kernel
def pointBounds16702 : List (Nat × Nat × Nat) := [(2193107968,97676245806528,97676624751854),(2193176576,97676658686621,97677037632213)]
theorem point_links_checked16702 : (cuts16702.take 2).map (fun c => (2193096705-1+2*2^9*c.k,97676182660518+c.lower,97676561605803+c.upper)) = pointBounds16702 := by
 decide +kernel
def cuts16703 : List PrefixCut := [⟨17,100488402,100488468⟩,
⟨84,504615874,504616203⟩,
⟨128,775011068,775011567⟩]
theorem checked16703 : checkPrefixCuts (2^48) 2193227777 9 Manual.Count131072.C016703.packed 128 cuts16703 = true := by
 decide +kernel
def pointBounds16703 : List (Nat × Nat × Nat) := [(2193245184,97677064623421,97677443569277),(2193313792,97677468750893,97677847697012)]
theorem point_links_checked16703 : (cuts16703.take 2).map (fun c => (2193227777-1+2*2^9*c.k,97676964135019+c.lower,97677343080809+c.upper)) = pointBounds16703 := by
 decide +kernel
def cuts16704 : List PrefixCut := [⟨23,139622865,139622952⟩,
⟨90,543981644,543981992⟩,
⟨128,776376365,776376859⟩]
theorem checked16704 : checkPrefixCuts (2^48) 2193358849 9 Manual.Count131072.C016704.packed 128 cuts16704 = true := by
 decide +kernel
def pointBounds16704 : List (Nat × Nat × Nat) := [(2193382400,97677878768952,97678257715328),(2193451008,97678283127731,97678662074368)]
theorem point_links_checked16704 : (cuts16704.take 2).map (fun c => (2193358849-1+2*2^9*c.k,97677739146087+c.lower,97678118092376+c.upper)) = pointBounds16704 := by
 decide +kernel
def cuts16705 : List PrefixCut := [⟨29,179265813,179265926⟩,
⟨96,588475426,588475798⟩,
⟨128,780308075,780308570⟩]
theorem checked16705 : checkPrefixCuts (2^48) 2193489921 9 Manual.Count131072.C016705.packed 128 cuts16705 = true := by
 decide +kernel
def pointBounds16705 : List (Nat × Nat × Nat) := [(2193519616,97678694788265,97679073735161),(2193588224,97679103997878,97679482945033)]
theorem point_links_checked16705 : (cuts16705.take 2).map (fun c => (2193489921-1+2*2^9*c.k,97678515522452+c.lower,97678894469235+c.upper)) = pointBounds16705 := by
 decide +kernel
def cuts16706 : List PrefixCut := [⟨35,214926180,214926314⟩,
⟨102,628216171,628216565⟩,
⟨128,787960003,787960498⟩]
theorem checked16706 : checkPrefixCuts (2^48) 2193620993 9 Manual.Count131072.C016706.packed 128 cuts16706 = true := by
 decide +kernel
def pointBounds16706 : List (Nat × Nat × Nat) := [(2193656832,97679510756707,97679889704119),(2193725440,97679924046698,97680302994370)]
theorem point_links_checked16706 : (cuts16706.take 2).map (fun c => (2193620993-1+2*2^9*c.k,97679295830527+c.lower,97679674777805+c.upper)) = pointBounds16706 := by
 decide +kernel
def cuts16707 : List PrefixCut := [⟨41,251993572,251993725⟩,
⟨108,661152074,661152484⟩,
⟨128,783550706,783551193⟩]
theorem checked16707 : checkPrefixCuts (2^48) 2193752065 9 Manual.Count131072.C016707.packed 128 cuts16707 = true := by
 decide +kernel
def pointBounds16707 : List (Nat × Nat × Nat) := [(2193794048,97680335784102,97680714732028),(2193862656,97680744942604,97681123890787)]
theorem point_links_checked16707 : (cuts16707.take 2).map (fun c => (2193752065-1+2*2^9*c.k,97680083790530+c.lower,97680462738303+c.upper)) = pointBounds16707 := by
 decide +kernel
def cuts16708 : List PrefixCut := [⟨47,287003644,287003826⟩,
⟨114,693313960,693314400⟩,
⟨128,778628546,778629041⟩]
theorem checked16708 : checkPrefixCuts (2^48) 2193883137 9 Manual.Count131072.C016708.packed 128 cuts16708 = true := by
 decide +kernel
def pointBounds16708 : List (Nat × Nat × Nat) := [(2193931264,97681154344880,97681533293322),(2193999872,97681560655196,97681939603896)]
theorem point_links_checked16708 : (cuts16708.take 2).map (fun c => (2193883137-1+2*2^9*c.k,97680867341236+c.lower,97681246289496+c.upper)) = pointBounds16708 := by
 decide +kernel
def cuts16709 : List PrefixCut := [⟨53,323677198,323677403⟩,
⟨120,729833856,729834311⟩,
⟨128,780891193,780891681⟩]
theorem checked16709 : checkPrefixCuts (2^48) 2194014209 9 Manual.Count131072.C016709.packed 128 cuts16709 = true := by
 decide +kernel
def pointBounds16709 : List (Nat × Nat × Nat) := [(2194068480,97681969646980,97682348595940),(2194137088,97682375803638,97682754752848)]
theorem point_links_checked16709 : (cuts16709.take 2).map (fun c => (2194014209-1+2*2^9*c.k,97681645969782+c.lower,97682024918537+c.upper)) = pointBounds16709 := by
 decide +kernel
def cuts16710 : List PrefixCut := [⟨59,365605863,365606093⟩,
⟨126,776226899,776227382⟩,
⟨128,788669761,788670252⟩]
theorem checked16710 : checkPrefixCuts (2^48) 2194145281 9 Manual.Count131072.C016710.packed 128 cuts16710 = true := by
 decide +kernel
def pointBounds16710 : List (Nat × Nat × Nat) := [(2194205696,97682792466838,97683171416311),(2194274304,97683203087874,97683582037600)]
theorem point_links_checked16710 : (cuts16710.take 2).map (fun c => (2194145281-1+2*2^9*c.k,97682426860975+c.lower,97682805810218+c.upper)) = pointBounds16710 := by
 decide +kernel
def cuts16711 : List PrefixCut := [⟨65,397780480,397780738⟩,
⟨128,779643512,779644009⟩]
theorem checked16711 : checkPrefixCuts (2^48) 2194276353 9 Manual.Count131072.C016711.packed 128 cuts16711 = true := by
 decide +kernel
def pointBounds16711 : List (Nat × Nat × Nat) := [(2194342912,97683613311216,97683992261208)]
theorem point_links_checked16711 : (cuts16711.take 1).map (fun c => (2194276353-1+2*2^9*c.k,97683215530736+c.lower,97683594480470+c.upper)) = pointBounds16711 := by
 decide +kernel
def cuts16712 : List PrefixCut := [⟨4,26038623,26038640⟩,
⟨71,431490443,431490717⟩,
⟨128,782546939,782547431⟩]
theorem checked16712 : checkPrefixCuts (2^48) 2194407425 9 Manual.Count131072.C016712.packed 128 cuts16712 = true := by
 decide +kernel
def pointBounds16712 : List (Nat × Nat × Nat) := [(2194411520,97684021212871,97684400163119),(2194480128,97684426664691,97684805615196)]
theorem point_links_checked16712 : (cuts16712.take 2).map (fun c => (2194407425-1+2*2^9*c.k,97683995174248+c.lower,97684374124479+c.upper)) = pointBounds16712 := by
 decide +kernel
def cuts16713 : List PrefixCut := [⟨10,64643666,64643708⟩,
⟨77,471352792,471353093⟩,
⟨128,785835057,785835554⟩]
theorem checked16713 : checkPrefixCuts (2^48) 2194538497 9 Manual.Count131072.C016713.packed 128 cuts16713 = true := by
 decide +kernel
def pointBounds16713 : List (Nat × Nat × Nat) := [(2194548736,97684842364853,97685221315618),(2194617344,97685249073979,97685628025003)]
theorem point_links_checked16713 : (cuts16713.take 2).map (fun c => (2194538497-1+2*2^9*c.k,97684777721187+c.lower,97685156671910+c.upper)) = pointBounds16713 := by
 decide +kernel
def cuts16714 : List PrefixCut := [⟨16,97216070,97216130⟩,
⟨83,509671024,509671346⟩,
⟨128,784120855,784121354⟩]
theorem checked16714 : checkPrefixCuts (2^48) 2194669569 9 Manual.Count131072.C016714.packed 128 cuts16714 = true := by
 decide +kernel
def pointBounds16714 : List (Nat × Nat × Nat) := [(2194685952,97685660772314,97686039723594),(2194754560,97686073227268,97686452178810)]
theorem point_links_checked16714 : (cuts16714.take 2).map (fun c => (2194669569-1+2*2^9*c.k,97685563556244+c.lower,97685942507464+c.upper)) = pointBounds16714 := by
 decide +kernel
def cuts16715 : List PrefixCut := [⟨22,132990650,132990736⟩,
⟨89,539648960,539649308⟩,
⟨128,779713764,779714262⟩]
theorem checked16715 : checkPrefixCuts (2^48) 2194800641 9 Manual.Count131072.C016715.packed 128 cuts16715 = true := by
 decide +kernel
def pointBounds16715 : List (Nat × Nat × Nat) := [(2194823168,97686480667749,97686859619554),(2194891776,97686887326059,97687266278126)]
theorem point_links_checked16715 : (cuts16715.take 2).map (fun c => (2194800641-1+2*2^9*c.k,97686347677099+c.lower,97686726628818+c.upper)) = pointBounds16715 := by
 decide +kernel
def cuts16716 : List PrefixCut := [⟨28,174275071,174275180⟩,
⟨95,580651449,580651811⟩,
⟨128,780564952,780565440⟩]
theorem checked16716 : checkPrefixCuts (2^48) 2194931713 9 Manual.Count131072.C016716.packed 128 cuts16716 = true := by
 decide +kernel
def pointBounds16716 : List (Nat × Nat × Nat) := [(2194960384,97687301665934,97687680618260),(2195028992,97687708042312,97688086994891)]
theorem point_links_checked16716 : (cuts16716.take 2).map (fun c => (2194931713-1+2*2^9*c.k,97687127390863+c.lower,97687506343080+c.upper)) = pointBounds16716 := by
 decide +kernel
def cuts16717 : List PrefixCut := [⟨34,207347719,207347842⟩,
⟨101,622161710,622162090⟩,
⟨128,788083639,788084122⟩]
theorem checked16717 : checkPrefixCuts (2^48) 2195062785 9 Manual.Count131072.C016717.packed 128 cuts16717 = true := by
 decide +kernel
def pointBounds16717 : List (Nat × Nat × Nat) := [(2195097600,97688115303534,97688494256362),(2195166208,97688530117525,97688909070610)]
theorem point_links_checked16717 : (cuts16717.take 2).map (fun c => (2195062785-1+2*2^9*c.k,97687907955815+c.lower,97688286908520+c.upper)) = pointBounds16717 := by
 decide +kernel
def cuts16718 : List PrefixCut := [⟨40,241698525,241698673⟩,
⟨107,651870617,651871026⟩,
⟨128,778548249,778548742⟩]
theorem checked16718 : checkPrefixCuts (2^48) 2195193857 9 Manual.Count131072.C016718.packed 128 cuts16718 = true := by
 decide +kernel
def pointBounds16718 : List (Nat × Nat × Nat) := [(2195234816,97688937737979,97689316691315),(2195303424,97689347910071,97689726863668)]
theorem point_links_checked16718 : (cuts16718.take 2).map (fun c => (2195193857-1+2*2^9*c.k,97688696039454+c.lower,97689074992642+c.upper)) = pointBounds16718 := by
 decide +kernel
def cuts16719 : List PrefixCut := [⟨46,280148079,280148253⟩,
⟨113,692346016,692346446⟩,
⟨128,785938136,785938626⟩]
theorem checked16719 : checkPrefixCuts (2^48) 2195324929 9 Manual.Count131072.C016719.packed 128 cuts16719 = true := by
 decide +kernel
def pointBounds16719 : List (Nat × Nat × Nat) := [(2195372032,97689754735782,97690133689637),(2195440640,97690166933719,97690545887830)]
theorem point_links_checked16719 : (cuts16719.take 2).map (fun c => (2195324929-1+2*2^9*c.k,97689474587703+c.lower,97689853541384+c.upper)) = pointBounds16719 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000209
