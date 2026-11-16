import PlattAssemblyKernel
import PlattCertificates.Count131072.C019792
import PlattCertificates.Count131072.C019793
import PlattCertificates.Count131072.C019794
import PlattCertificates.Count131072.C019795
import PlattCertificates.Count131072.C019796
import PlattCertificates.Count131072.C019797
import PlattCertificates.Count131072.C019798
import PlattCertificates.Count131072.C019799
import PlattCertificates.Count131072.C019800
import PlattCertificates.Count131072.C019801
import PlattCertificates.Count131072.C019802
import PlattCertificates.Count131072.C019803
import PlattCertificates.Count131072.C019804
import PlattCertificates.Count131072.C019805
import PlattCertificates.Count131072.C019806
import PlattCertificates.Count131072.C019807
import PlattCertificates.Count131072.C019808
import PlattCertificates.Count131072.C019809
import PlattCertificates.Count131072.C019810
import PlattCertificates.Count131072.C019811
import PlattCertificates.Count131072.C019812
import PlattCertificates.Count131072.C019813
import PlattCertificates.Count131072.C019814
import PlattCertificates.Count131072.C019815
import PlattCertificates.Count131072.C019816
import PlattCertificates.Count131072.C019817
import PlattCertificates.Count131072.C019818
import PlattCertificates.Count131072.C019819
import PlattCertificates.Count131072.C019820
import PlattCertificates.Count131072.C019821
import PlattCertificates.Count131072.C019822
import PlattCertificates.Count131072.C019823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000306
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19792 : List PrefixCut := [⟨29,151239481,151239571⟩,
⟨109,558147241,558147577⟩,
⟨128,651747214,651747606⟩]
theorem checked19792 : checkPrefixCuts (2^48) 2598109185 9 Manual.Count131072.C019792.packed 128 cuts19792 = true := by
 decide +kernel
def pointBounds19792 : List (Nat × Nat × Nat) := [(2598138880,99885554190735,99885934480829),(2598220800,99885961098495,99886341388835)]
theorem point_links_checked19792 : (cuts19792.take 2).map (fun c => (2598109185-1+2*2^9*c.k,99885402951254+c.lower,99885783241258+c.upper)) = pointBounds19792 := by
 decide +kernel
def cuts19793 : List PrefixCut := [⟨61,308853340,308853523⟩,
⟨128,663847002,663847393⟩]
theorem checked19793 : checkPrefixCuts (2^48) 2598240257 9 Manual.Count131072.C019793.packed 128 cuts19793 = true := by
 decide +kernel
def pointBounds19793 : List (Nat × Nat × Nat) := [(2598302720,99886363551808,99886743842387)]
theorem point_links_checked19793 : (cuts19793.take 1).map (fun c => (2598240257-1+2*2^9*c.k,99886054698468+c.lower,99886434988864+c.upper)) = pointBounds19793 := by
 decide +kernel
def cuts19794 : List PrefixCut := [⟨13,63804694,63804732⟩,
⟨93,470240758,470241039⟩,
⟨128,654172730,654173117⟩]
theorem checked19794 : checkPrefixCuts (2^48) 2598371329 9 Manual.Count131072.C019794.packed 128 cuts19794 = true := by
 decide +kernel
def pointBounds19794 : List (Nat × Nat × Nat) := [(2598384640,99886782350164,99887162640989),(2598466560,99887188786228,99887569077296)]
theorem point_links_checked19794 : (cuts19794.take 2).map (fun c => (2598371329-1+2*2^9*c.k,99886718545470+c.lower,99887098836257+c.upper)) = pointBounds19794 := by
 decide +kernel
def cuts19795 : List PrefixCut := [⟨45,227799083,227799216⟩,
⟨125,634534353,634534731⟩,
⟨128,650348573,650348960⟩]
theorem checked19795 : checkPrefixCuts (2^48) 2598502401 9 Manual.Count131072.C019795.packed 128 cuts19795 = true := by
 decide +kernel
def pointBounds19795 : List (Nat × Nat × Nat) := [(2598548480,99887600517283,99887980808590),(2598630400,99888007252553,99888387544105)]
theorem point_links_checked19795 : (cuts19795.take 2).map (fun c => (2598502401-1+2*2^9*c.k,99887372718200+c.lower,99887753009374+c.upper)) = pointBounds19795 := by
 decide +kernel
def cuts19796 : List PrefixCut := [⟨77,397407231,397407471⟩,
⟨128,656706420,656706813⟩]
theorem checked19796 : checkPrefixCuts (2^48) 2598633473 9 Manual.Count131072.C019796.packed 128 cuts19796 = true := by
 decide +kernel
def pointBounds19796 : List (Nat × Nat × Nat) := [(2598712320,99888420474004,99888800765805)]
theorem point_links_checked19796 : (cuts19796.take 1).map (fun c => (2598633473-1+2*2^9*c.k,99888023066773+c.lower,99888403358334+c.upper)) = pointBounds19796 := by
 decide +kernel
def cuts19797 : List PrefixCut := [⟨29,150118260,150118346⟩,
⟨109,553890836,553891155⟩,
⟨128,652449287,652449664⟩]
theorem checked19797 : checkPrefixCuts (2^48) 2598764545 9 Manual.Count131072.C019797.packed 128 cuts19797 = true := by
 decide +kernel
def pointBounds19797 : List (Nat × Nat × Nat) := [(2598794240,99888829891453,99889210183493),(2598876160,99889233664029,99889613956302)]
theorem point_links_checked19797 : (cuts19797.take 2).map (fun c => (2598764545-1+2*2^9*c.k,99888679773193+c.lower,99889060065147+c.upper)) = pointBounds19797 := by
 decide +kernel
def cuts19798 : List PrefixCut := [⟨61,314298968,314299150⟩,
⟨128,662271856,662272247⟩]
theorem checked19798 : checkPrefixCuts (2^48) 2598895617 9 Manual.Count131072.C019798.packed 128 cuts19798 = true := by
 decide +kernel
def pointBounds19798 : List (Nat × Nat × Nat) := [(2598958080,99889646521448,99890026813961)]
theorem point_links_checked19798 : (cuts19798.take 1).map (fun c => (2598895617-1+2*2^9*c.k,99889332222480+c.lower,99889712514811+c.upper)) = pointBounds19798 := by
 decide +kernel
def cuts19799 : List PrefixCut := [⟨13,68770398,68770437⟩,
⟨93,481385234,481385521⟩,
⟨128,661155604,661155999⟩]
theorem checked19799 : checkPrefixCuts (2^48) 2599026689 9 Manual.Count131072.C019799.packed 128 cuts19799 = true := by
 decide +kernel
def pointBounds19799 : List (Nat × Nat × Nat) := [(2599040000,99890063264734,99890443557495),(2599121920,99890475879570,99890856172579)]
theorem point_links_checked19799 : (cuts19799.take 2).map (fun c => (2599026689-1+2*2^9*c.k,99889994494336+c.lower,99890374787058+c.upper)) = pointBounds19799 := by
 decide +kernel
def cuts19800 : List PrefixCut := [⟨45,230773877,230774013⟩,
⟨125,632641812,632642189⟩,
⟨128,649534937,649535323⟩]
theorem checked19800 : checkPrefixCuts (2^48) 2599157761 9 Manual.Count131072.C019800.packed 128 cuts19800 = true := by
 decide +kernel
def pointBounds19800 : List (Nat × Nat × Nat) := [(2599203840,99890886423817,99891266717070),(2599285760,99891288291752,99891668585246)]
theorem point_links_checked19800 : (cuts19800.take 2).map (fun c => (2599157761-1+2*2^9*c.k,99890655649940+c.lower,99891035943057+c.upper)) = pointBounds19800 := by
 decide +kernel
def cuts19801 : List PrefixCut := [⟨77,394274848,394275087⟩,
⟨128,660872081,660872472⟩]
theorem checked19801 : checkPrefixCuts (2^48) 2599288833 9 Manual.Count131072.C019801.packed 128 cuts19801 = true := by
 decide +kernel
def pointBounds19801 : List (Nat × Nat × Nat) := [(2599367680,99891699459725,99892079753467)]
theorem point_links_checked19801 : (cuts19801.take 1).map (fun c => (2599288833-1+2*2^9*c.k,99891305184877+c.lower,99891685478380+c.upper)) = pointBounds19801 := by
 decide +kernel
def cuts19802 : List PrefixCut := [⟨29,143150271,143150354⟩,
⟨109,555808263,555808593⟩,
⟨128,652176282,652176667⟩]
theorem checked19802 : checkPrefixCuts (2^48) 2599419905 9 Manual.Count131072.C019802.packed 128 cuts19802 = true := by
 decide +kernel
def pointBounds19802 : List (Nat × Nat × Nat) := [(2599449600,99892109207229,99892489501206),(2599531520,99892521865221,99892902159445)]
theorem point_links_checked19802 : (cuts19802.take 2).map (fun c => (2599419905-1+2*2^9*c.k,99891966056958+c.lower,99892346350852+c.upper)) = pointBounds19802 := by
 decide +kernel
def cuts19803 : List PrefixCut := [⟨61,316493642,316493833⟩,
⟨128,653009897,653010285⟩]
theorem checked19803 : checkPrefixCuts (2^48) 2599550977 9 Manual.Count131072.C019803.packed 128 cuts19803 = true := by
 decide +kernel
def pointBounds19803 : List (Nat × Nat × Nat) := [(2599613440,99892934726882,99893315021352)]
theorem point_links_checked19803 : (cuts19803.take 1).map (fun c => (2599550977-1+2*2^9*c.k,99892618233240+c.lower,99892998527519+c.upper)) = pointBounds19803 := by
 decide +kernel
def cuts19804 : List PrefixCut := [⟨13,67453791,67453832⟩,
⟨93,475308943,475309227⟩,
⟨128,658065509,658065896⟩]
theorem checked19804 : checkPrefixCuts (2^48) 2599682049 9 Manual.Count131072.C019804.packed 128 cuts19804 = true := by
 decide +kernel
def pointBounds19804 : List (Nat × Nat × Nat) := [(2599695360,99893338696928,99893718991636),(2599777280,99893746552080,99894126847031)]
theorem point_links_checked19804 : (cuts19804.take 2).map (fun c => (2599682049-1+2*2^9*c.k,99893271243137+c.lower,99893651537804+c.upper)) = pointBounds19804 := by
 decide +kernel
def cuts19805 : List PrefixCut := [⟨45,230932246,230932379⟩,
⟨125,635730297,635730672⟩,
⟨128,650670447,650670832⟩]
theorem checked19805 : checkPrefixCuts (2^48) 2599813121 9 Manual.Count131072.C019805.packed 128 cuts19805 = true := by
 decide +kernel
def pointBounds19805 : List (Nat × Nat × Nat) := [(2599859200,99894160240892,99894540536079),(2599941120,99894565038943,99894945334372)]
theorem point_links_checked19805 : (cuts19805.take 2).map (fun c => (2599813121-1+2*2^9*c.k,99893929308646+c.lower,99894309603700+c.upper)) = pointBounds19805 := by
 decide +kernel
def cuts19806 : List PrefixCut := [⟨77,388979137,388979372⟩,
⟨128,653560560,653560944⟩]
theorem checked19806 : checkPrefixCuts (2^48) 2599944193 9 Manual.Count131072.C019806.packed 128 cuts19806 = true := by
 decide +kernel
def pointBounds19806 : List (Nat × Nat × Nat) := [(2600023040,99894968958230,99895349253904)]
theorem point_links_checked19806 : (cuts19806.take 1).map (fun c => (2599944193-1+2*2^9*c.k,99894579979093+c.lower,99894960274532+c.upper)) = pointBounds19806 := by
 decide +kernel
def cuts19807 : List PrefixCut := [⟨29,148960016,148960103⟩,
⟨109,562271812,562272138⟩,
⟨128,654393751,654394132⟩]
theorem checked19807 : checkPrefixCuts (2^48) 2600075265 9 Manual.Count131072.C019807.packed 128 cuts19807 = true := by
 decide +kernel
def pointBounds19807 : List (Nat × Nat × Nat) := [(2600104960,99895382499669,99895762795579),(2600186880,99895795811465,99896176107614)]
theorem point_links_checked19807 : (cuts19807.take 2).map (fun c => (2600075265-1+2*2^9*c.k,99895233539653+c.lower,99895613835476+c.upper)) = pointBounds19807 := by
 decide +kernel
def cuts19808 : List PrefixCut := [⟨61,312949785,312949968⟩,
⟨128,656309104,656309488⟩]
theorem checked19808 : checkPrefixCuts (2^48) 2600206337 9 Manual.Count131072.C019808.packed 128 cuts19808 = true := by
 decide +kernel
def pointBounds19808 : List (Nat × Nat × Nat) := [(2600268800,99896200883189,99896581179576)]
theorem point_links_checked19808 : (cuts19808.take 1).map (fun c => (2600206337-1+2*2^9*c.k,99895887933404+c.lower,99896268229608+c.upper)) = pointBounds19808 := by
 decide +kernel
def cuts19809 : List PrefixCut := [⟨13,68194505,68194545⟩,
⟨93,478436525,478436802⟩,
⟨128,657575074,657575462⟩]
theorem checked19809 : checkPrefixCuts (2^48) 2600337409 9 Manual.Count131072.C019809.packed 128 cuts19809 = true := by
 decide +kernel
def pointBounds19809 : List (Nat × Nat × Nat) := [(2600350720,99896612437013,99896992733641),(2600432640,99897022679033,99897402975898)]
theorem point_links_checked19809 : (cuts19809.take 2).map (fun c => (2600337409-1+2*2^9*c.k,99896544242508+c.lower,99896924539096+c.upper)) = pointBounds19809 := by
 decide +kernel
def cuts19810 : List PrefixCut := [⟨45,230549324,230549461⟩,
⟨125,643038401,643038782⟩,
⟨128,657758317,657758707⟩]
theorem checked19810 : checkPrefixCuts (2^48) 2600468481 9 Manual.Count131072.C019810.packed 128 cuts19810 = true := by
 decide +kernel
def pointBounds19810 : List (Nat × Nat × Nat) := [(2600514560,99897432366906,99897812664019),(2600596480,99897844855983,99898225153340)]
theorem point_links_checked19810 : (cuts19810.take 2).map (fun c => (2600468481-1+2*2^9*c.k,99897201817582+c.lower,99897582114558+c.upper)) = pointBounds19810 := by
 decide +kernel
def cuts19811 : List PrefixCut := [⟨77,392452726,392452956⟩,
⟨128,650148937,650149317⟩]
theorem checked19811 : checkPrefixCuts (2^48) 2600599553 9 Manual.Count131072.C019811.packed 128 cuts19811 = true := by
 decide +kernel
def pointBounds19811 : List (Nat × Nat × Nat) := [(2600678400,99898252028625,99898632326221)]
theorem point_links_checked19811 : (cuts19811.take 1).map (fun c => (2600599553-1+2*2^9*c.k,99897859575899+c.lower,99898239873265+c.upper)) = pointBounds19811 := by
 decide +kernel
def cuts19812 : List PrefixCut := [⟨29,146433216,146433303⟩,
⟨109,556935193,556935523⟩,
⟨128,653362882,653363269⟩]
theorem checked19812 : checkPrefixCuts (2^48) 2600730625 9 Manual.Count131072.C019812.packed 128 cuts19812 = true := by
 decide +kernel
def pointBounds19812 : List (Nat × Nat × Nat) := [(2600760320,99898656158052,99899036455885),(2600842240,99899066660029,99899446958105)]
theorem point_links_checked19812 : (cuts19812.take 2).map (fun c => (2600730625-1+2*2^9*c.k,99898509724836+c.lower,99898890022582+c.upper)) = pointBounds19812 := by
 decide +kernel
def cuts19813 : List PrefixCut := [⟨61,309299635,309299820⟩,
⟨128,650840917,650841297⟩]
theorem checked19813 : checkPrefixCuts (2^48) 2600861697 9 Manual.Count131072.C019813.packed 128 cuts19813 = true := by
 decide +kernel
def pointBounds19813 : List (Nat × Nat × Nat) := [(2600924160,99899472387353,99899852685671)]
theorem point_links_checked19813 : (cuts19813.take 1).map (fun c => (2600861697-1+2*2^9*c.k,99899163087718+c.lower,99899543385851+c.upper)) = pointBounds19813 := by
 decide +kernel
def cuts19814 : List PrefixCut := [⟨13,66337617,66337654⟩,
⟨93,476476219,476476496⟩,
⟨128,655894307,655894688⟩]
theorem checked19814 : checkPrefixCuts (2^48) 2600992769 9 Manual.Count131072.C019814.packed 128 cuts19814 = true := by
 decide +kernel
def pointBounds19814 : List (Nat × Nat × Nat) := [(2601006080,99899880266252,99900260564802),(2601088000,99900290404854,99900670703644)]
theorem point_links_checked19814 : (cuts19814.take 2).map (fun c => (2600992769-1+2*2^9*c.k,99899813928635+c.lower,99900194227148+c.upper)) = pointBounds19814 := by
 decide +kernel
def cuts19815 : List PrefixCut := [⟨45,221509640,221509775⟩,
⟨125,625779168,625779537⟩,
⟨128,640711791,640712169⟩]
theorem checked19815 : checkPrefixCuts (2^48) 2601123841 9 Manual.Count131072.C019815.packed 128 cuts19815 = true := by
 decide +kernel
def pointBounds19815 : List (Nat × Nat × Nat) := [(2601169920,99900691332582,99901071631611),(2601251840,99901095602110,99901475901373)]
theorem point_links_checked19815 : (cuts19815.take 2).map (fun c => (2601123841-1+2*2^9*c.k,99900469822942+c.lower,99900850121836+c.upper)) = pointBounds19815 := by
 decide +kernel
def cuts19816 : List PrefixCut := [⟨77,390189724,390189958⟩,
⟨128,652473725,652474111⟩]
theorem checked19816 : checkPrefixCuts (2^48) 2601254913 9 Manual.Count131072.C019816.packed 128 cuts19816 = true := by
 decide +kernel
def pointBounds19816 : List (Nat × Nat × Nat) := [(2601333760,99901500724457,99901881023963)]
theorem point_links_checked19816 : (cuts19816.take 1).map (fun c => (2601254913-1+2*2^9*c.k,99901110534733+c.lower,99901490834005+c.upper)) = pointBounds19816 := by
 decide +kernel
def cuts19817 : List PrefixCut := [⟨29,142068304,142068387⟩,
⟨109,543053620,543053947⟩,
⟨128,642594723,642595108⟩]
theorem checked19817 : checkPrefixCuts (2^48) 2601385985 9 Manual.Count131072.C019817.packed 128 cuts19817 = true := by
 decide +kernel
def pointBounds19817 : List (Nat × Nat × Nat) := [(2601415680,99901905076762,99902285376503),(2601497600,99902306062078,99902686362063)]
theorem point_links_checked19817 : (cuts19817.take 2).map (fun c => (2601385985-1+2*2^9*c.k,99901763008458+c.lower,99902143308116+c.upper)) = pointBounds19817 := by
 decide +kernel
def cuts19818 : List PrefixCut := [⟨61,313008559,313008743⟩,
⟨128,663443759,663444143⟩]
theorem checked19818 : checkPrefixCuts (2^48) 2601517057 9 Manual.Count131072.C019818.packed 128 cuts19818 = true := by
 decide +kernel
def pointBounds19818 : List (Nat × Nat × Nat) := [(2601579520,99902718611740,99903098911967)]
theorem point_links_checked19818 : (cuts19818.take 1).map (fun c => (2601517057-1+2*2^9*c.k,99902405603181+c.lower,99902785903224+c.upper)) = pointBounds19818 := by
 decide +kernel
def cuts19819 : List PrefixCut := [⟨13,63940710,63940748⟩,
⟨93,477438038,477438321⟩,
⟨128,658109141,658109532⟩]
theorem checked19819 : checkPrefixCuts (2^48) 2601648129 9 Manual.Count131072.C019819.packed 128 cuts19819 = true := by
 decide +kernel
def pointBounds19819 : List (Nat × Nat × Nat) := [(2601661440,99903132987650,99903513288115),(2601743360,99903546484978,99903926785688)]
theorem point_links_checked19819 : (cuts19819.take 2).map (fun c => (2601648129-1+2*2^9*c.k,99903069046940+c.lower,99903449347367+c.upper)) = pointBounds19819 := by
 decide +kernel
def cuts19820 : List PrefixCut := [⟨45,224591159,224591294⟩,
⟨125,634167942,634168322⟩,
⟨128,649962246,649962634⟩]
theorem checked19820 : checkPrefixCuts (2^48) 2601779201 9 Manual.Count131072.C019820.packed 128 cuts19820 = true := by
 decide +kernel
def pointBounds19820 : List (Nat × Nat × Nat) := [(2601825280,99903951747240,99904332048193),(2601907200,99904361324023,99904741625221)]
theorem point_links_checked19820 : (cuts19820.take 2).map (fun c => (2601779201-1+2*2^9*c.k,99903727156081+c.lower,99904107456899+c.upper)) = pointBounds19820 := by
 decide +kernel
def cuts19821 : List PrefixCut := [⟨77,390632338,390632571⟩,
⟨128,653174834,653175220⟩]
theorem checked19821 : checkPrefixCuts (2^48) 2601910273 9 Manual.Count131072.C019821.packed 128 cuts19821 = true := by
 decide +kernel
def pointBounds19821 : List (Nat × Nat × Nat) := [(2601989120,99904767750665,99905148052104)]
theorem point_links_checked19821 : (cuts19821.take 1).map (fun c => (2601910273-1+2*2^9*c.k,99904377118327+c.lower,99904757419533+c.upper)) = pointBounds19821 := by
 decide +kernel
def cuts19822 : List PrefixCut := [⟨29,151551816,151551908⟩,
⟨109,560440900,560441230⟩,
⟨128,656279161,656279546⟩]
theorem checked19822 : checkPrefixCuts (2^48) 2602041345 9 Manual.Count131072.C019822.packed 128 cuts19822 = true := by
 decide +kernel
def pointBounds19822 : List (Nat × Nat × Nat) := [(2602071040,99905181844977,99905562146661),(2602152960,99905590734061,99905971035983)]
theorem point_links_checked19822 : (cuts19822.take 2).map (fun c => (2602041345-1+2*2^9*c.k,99905030293161+c.lower,99905410594753+c.upper)) = pointBounds19822 := by
 decide +kernel
def cuts19823 : List PrefixCut := [⟨61,312064383,312064565⟩,
⟨128,650513178,650513560⟩]
theorem checked19823 : checkPrefixCuts (2^48) 2602172417 9 Manual.Count131072.C019823.packed 128 cuts19823 = true := by
 decide +kernel
def pointBounds19823 : List (Nat × Nat × Nat) := [(2602234880,99905998636705,99906378938864)]
theorem point_links_checked19823 : (cuts19823.take 1).map (fun c => (2602172417-1+2*2^9*c.k,99905686572322+c.lower,99906066874299+c.upper)) = pointBounds19823 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000306
