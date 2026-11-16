import PlattAssemblyKernel
import PlattCertificates.Count131072.C011728
import PlattCertificates.Count131072.C011729
import PlattCertificates.Count131072.C011730
import PlattCertificates.Count131072.C011731
import PlattCertificates.Count131072.C011732
import PlattCertificates.Count131072.C011733
import PlattCertificates.Count131072.C011734
import PlattCertificates.Count131072.C011735
import PlattCertificates.Count131072.C011736
import PlattCertificates.Count131072.C011737
import PlattCertificates.Count131072.C011738
import PlattCertificates.Count131072.C011739
import PlattCertificates.Count131072.C011740
import PlattCertificates.Count131072.C011741
import PlattCertificates.Count131072.C011742
import PlattCertificates.Count131072.C011743
import PlattCertificates.Count131072.C011744
import PlattCertificates.Count131072.C011745
import PlattCertificates.Count131072.C011746
import PlattCertificates.Count131072.C011747
import PlattCertificates.Count131072.C011748
import PlattCertificates.Count131072.C011749
import PlattCertificates.Count131072.C011750
import PlattCertificates.Count131072.C011751
import PlattCertificates.Count131072.C011752
import PlattCertificates.Count131072.C011753
import PlattCertificates.Count131072.C011754
import PlattCertificates.Count131072.C011755
import PlattCertificates.Count131072.C011756
import PlattCertificates.Count131072.C011757
import PlattCertificates.Count131072.C011758
import PlattCertificates.Count131072.C011759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11728 : List PrefixCut := [⟨9,80726693,80726758⟩,
⟨57,497685024,497685410⟩,
⟨105,922665729,922666444⟩,
⟨128,1131407253,1131408130⟩]
theorem checked11728 : checkPrefixCuts (2^48) 1541144577 9 Manual.Count131072.C011728.packed 128 cuts11728 = true := by
 decide +kernel
def pointBounds11728 : List (Nat × Nat × Nat) := [(1541153792,93021297008736,93021672710107),(1541202944,93021713967067,93022089668759),(1541252096,93022138947772,93022514649793)]
theorem point_links_checked11728 : (cuts11728.take 3).map (fun c => (1541144577-1+2*2^9*c.k,93021216282043+c.lower,93021591983349+c.upper)) = pointBounds11728 := by
 decide +kernel
def cuts11729 : List PrefixCut := [⟨25,228461464,228461642⟩,
⟨73,641910184,641910684⟩,
⟨121,1063198159,1063198986⟩,
⟨128,1126381048,1126381925⟩]
theorem checked11729 : checkPrefixCuts (2^48) 1541275649 9 Manual.Count131072.C011729.packed 128 cuts11729 = true := by
 decide +kernel
def pointBounds11729 : List (Nat × Nat × Nat) := [(1541301248,93022576150760,93022951853121),(1541350400,93022989599480,93023365302163),(1541399552,93023410887455,93023786590465)]
theorem point_links_checked11729 : (cuts11729.take 3).map (fun c => (1541275649-1+2*2^9*c.k,93022347689296+c.lower,93022723391479+c.upper)) = pointBounds11729 := by
 decide +kernel
def cuts11730 : List PrefixCut := [⟨41,365943605,365943888⟩,
⟨89,788482664,788483277⟩,
⟨128,1125189537,1125190410⟩]
theorem checked11730 : checkPrefixCuts (2^48) 1541406721 9 Manual.Count131072.C011730.packed 128 cuts11730 = true := by
 decide +kernel
def pointBounds11730 : List (Nat × Nat × Nat) := [(1541448704,93023840013949,93024215717292),(1541497856,93024262553008,93024638256681)]
theorem point_links_checked11730 : (cuts11730.take 2).map (fun c => (1541406721-1+2*2^9*c.k,93023474070344+c.lower,93023849773404+c.upper)) = pointBounds11730 := by
 decide +kernel
def cuts11731 : List PrefixCut := [⟨9,83079825,83079890⟩,
⟨57,508878598,508878994⟩,
⟨105,938315563,938316293⟩,
⟨128,1138240034,1138240923⟩]
theorem checked11731 : checkPrefixCuts (2^48) 1541537793 9 Manual.Count131072.C011731.packed 128 cuts11731 = true := by
 decide +kernel
def pointBounds11731 : List (Nat × Nat × Nat) := [(1541547008,93024682339706,93025058043704),(1541596160,93025108138479,93025483842808),(1541645312,93025537575444,93025913280107)]
theorem point_links_checked11731 : (cuts11731.take 3).map (fun c => (1541537793-1+2*2^9*c.k,93024599259881+c.lower,93024974963814+c.upper)) = pointBounds11731 := by
 decide +kernel
def cuts11732 : List PrefixCut := [⟨25,219456980,219457148⟩,
⟨73,652517864,652518369⟩,
⟨121,1082096309,1082097147⟩,
⟨128,1142342074,1142342960⟩]
theorem checked11732 : checkPrefixCuts (2^48) 1541668865 9 Manual.Count131072.C011732.packed 128 cuts11732 = true := by
 decide +kernel
def pointBounds11732 : List (Nat × Nat × Nat) := [(1541694464,93025956956895,93026332661885),(1541743616,93026390017779,93026765723106),(1541792768,93026819596224,93027195301884)]
theorem point_links_checked11732 : (cuts11732.take 3).map (fun c => (1541668865-1+2*2^9*c.k,93025737499915+c.lower,93026113204737+c.upper)) = pointBounds11732 := by
 decide +kernel
def cuts11733 : List PrefixCut := [⟨41,366580544,366580829⟩,
⟨89,805259386,805260008⟩,
⟨128,1146444155,1146445045⟩]
theorem checked11733 : checkPrefixCuts (2^48) 1541799937 9 Manual.Count131072.C011733.packed 128 cuts11733 = true := by
 decide +kernel
def pointBounds11733 : List (Nat × Nat × Nat) := [(1541841920,93027246422533,93027622128526),(1541891072,93027685101375,93028060807705)]
theorem point_links_checked11733 : (cuts11733.take 2).map (fun c => (1541799937-1+2*2^9*c.k,93026879841989+c.lower,93027255547697+c.upper)) = pointBounds11733 := by
 decide +kernel
def cuts11734 : List PrefixCut := [⟨9,76486958,76487017⟩,
⟨57,496153398,496153784⟩,
⟨105,910330143,910330853⟩,
⟨128,1114219373,1114220240⟩]
theorem checked11734 : checkPrefixCuts (2^48) 1541931009 9 Manual.Count131072.C011734.packed 128 cuts11734 = true := by
 decide +kernel
def pointBounds11734 : List (Nat × Nat × Nat) := [(1541940224,93028102773102,93028478479759),(1541989376,93028522439542,93028898146526),(1542038528,93028936616287,93029312323595)]
theorem point_links_checked11734 : (cuts11734.take 3).map (fun c => (1541931009-1+2*2^9*c.k,93028026286144+c.lower,93028401992742+c.upper)) = pointBounds11734 := by
 decide +kernel
def cuts11735 : List PrefixCut := [⟨25,225972102,225972277⟩,
⟨73,643590539,643591043⟩,
⟨121,1068861438,1068862266⟩,
⟨128,1130369461,1130370337⟩]
theorem checked11735 : checkPrefixCuts (2^48) 1542062081 9 Manual.Count131072.C011735.packed 128 cuts11735 = true := by
 decide +kernel
def pointBounds11735 : List (Nat × Nat × Nat) := [(1542087680,93029366477619,93029742185259),(1542136832,93029784096056,93030159804025),(1542185984,93030209366955,93030585075248)]
theorem point_links_checked11735 : (cuts11735.take 3).map (fun c => (1542062081-1+2*2^9*c.k,93029140505517+c.lower,93029516212982+c.upper)) = pointBounds11735 := by
 decide +kernel
def cuts11736 : List PrefixCut := [⟨41,360281640,360281922⟩,
⟨89,786985601,786986213⟩,
⟨128,1136661070,1136661953⟩]
theorem checked11736 : checkPrefixCuts (2^48) 1542193153 9 Manual.Count131072.C011736.packed 128 cuts11736 = true := by
 decide +kernel
def pointBounds11736 : List (Nat × Nat × Nat) := [(1542235136,93030631156618,93031006865241),(1542284288,93031057860579,93031433569532)]
theorem point_links_checked11736 : (cuts11736.take 2).map (fun c => (1542193153-1+2*2^9*c.k,93030270874978+c.lower,93030646583319+c.upper)) = pointBounds11736 := by
 decide +kernel
def cuts11737 : List PrefixCut := [⟨9,83584959,83585021⟩,
⟨57,499676942,499677333⟩,
⟨105,923055226,923055947⟩,
⟨128,1129264779,1129265658⟩]
theorem checked11737 : checkPrefixCuts (2^48) 1542324225 9 Manual.Count131072.C011737.packed 128 cuts11737 = true := by
 decide +kernel
def pointBounds11737 : List (Nat × Nat × Nat) := [(1542333440,93031491121007,93031866830293),(1542382592,93031907212990,93032282922605),(1542431744,93032330591274,93032706301219)]
theorem point_links_checked11737 : (cuts11737.take 3).map (fun c => (1542324225-1+2*2^9*c.k,93031407536048+c.lower,93031783245272+c.upper)) = pointBounds11737 := by
 decide +kernel
def cuts11738 : List PrefixCut := [⟨25,220622458,220622627⟩,
⟨73,647988355,647988860⟩,
⟨121,1065122138,1065122974⟩,
⟨128,1125337193,1125338076⟩]
theorem checked11738 : checkPrefixCuts (2^48) 1542455297 9 Manual.Count131072.C011738.packed 128 cuts11738 = true := by
 decide +kernel
def pointBounds11738 : List (Nat × Nat × Nat) := [(1542480896,93032757423285,93033133133557),(1542530048,93033184789182,93033560499790),(1542579200,93033601922965,93033977633904)]
theorem point_links_checked11738 : (cuts11738.take 3).map (fun c => (1542455297-1+2*2^9*c.k,93032536800827+c.lower,93032912510930+c.upper)) = pointBounds11738 := by
 decide +kernel
def cuts11739 : List PrefixCut := [⟨41,367670917,367671200⟩,
⟨89,793171256,793171870⟩,
⟨128,1138925926,1138926806⟩]
theorem checked11739 : checkPrefixCuts (2^48) 1542586369 9 Manual.Count131072.C011739.packed 128 cuts11739 = true := by
 decide +kernel
def pointBounds11739 : List (Nat × Nat × Nat) := [(1542628352,93034029808937,93034405520206),(1542677504,93034455309276,93034831020876)]
theorem point_links_checked11739 : (cuts11739.take 2).map (fun c => (1542586369-1+2*2^9*c.k,93033662138020+c.lower,93034037849006+c.upper)) = pointBounds11739 := by
 decide +kernel
def cuts11740 : List PrefixCut := [⟨9,82468939,82469002⟩,
⟨57,501556379,501556771⟩,
⟨105,927745822,927746547⟩,
⟨128,1130618902,1130619787⟩]
theorem checked11740 : checkPrefixCuts (2^48) 1542717441 9 Manual.Count131072.C011740.packed 128 cuts11740 = true := by
 decide +kernel
def pointBounds11740 : List (Nat × Nat × Nat) := [(1542726656,93034883532885,93035259244814),(1542775808,93035302620325,93035678332583),(1542824960,93035728809768,93036104522359)]
theorem point_links_checked11740 : (cuts11740.take 3).map (fun c => (1542717441-1+2*2^9*c.k,93034801063946+c.lower,93035176775812+c.upper)) = pointBounds11740 := by
 decide +kernel
def cuts11741 : List PrefixCut := [⟨25,219289175,219289343⟩,
⟨73,636512102,636512595⟩,
⟨121,1060289392,1060290212⟩,
⟨128,1122860607,1122861475⟩]
theorem checked11741 : checkPrefixCuts (2^48) 1542848513 9 Manual.Count131072.C011741.packed 128 cuts11741 = true := by
 decide +kernel
def pointBounds11741 : List (Nat × Nat × Nat) := [(1542874112,93036150972023,93036526684942),(1542923264,93036568194950,93036943908194),(1542972416,93036991972240,93037367685811)]
theorem point_links_checked11741 : (cuts11741.take 3).map (fun c => (1542848513-1+2*2^9*c.k,93035931682848+c.lower,93036307395599+c.upper)) = pointBounds11741 := by
 decide +kernel
def cuts11742 : List PrefixCut := [⟨41,362834257,362834539⟩,
⟨89,791327246,791327858⟩,
⟨128,1137723457,1137724342⟩]
theorem checked11742 : checkPrefixCuts (2^48) 1542979585 9 Manual.Count131072.C011742.packed 128 cuts11742 = true := by
 decide +kernel
def pointBounds11742 : List (Nat × Nat × Nat) := [(1543021568,93037417377712,93037793091613),(1543070720,93037845870701,93038221584932)]
theorem point_links_checked11742 : (cuts11742.take 2).map (fun c => (1542979585-1+2*2^9*c.k,93037054543455+c.lower,93037430257074+c.upper)) = pointBounds11742 := by
 decide +kernel
def cuts11743 : List PrefixCut := [⟨9,80259033,80259094⟩,
⟨57,500151847,500152236⟩,
⟨105,920213667,920214383⟩,
⟨128,1125041392,1125042267⟩]
theorem checked11743 : checkPrefixCuts (2^48) 1543110657 9 Manual.Count131072.C011743.packed 128 cuts11743 = true := by
 decide +kernel
def pointBounds11743 : List (Nat × Nat × Nat) := [(1543119872,93038272525945,93038648240510),(1543169024,93038692418759,93039068133652),(1543218176,93039112480579,93039488195799)]
theorem point_links_checked11743 : (cuts11743.take 3).map (fun c => (1543110657-1+2*2^9*c.k,93038192266912+c.lower,93038567981416+c.upper)) = pointBounds11743 := by
 decide +kernel
def cuts11744 : List PrefixCut := [⟨25,224887417,224887595⟩,
⟨73,643828073,643828577⟩,
⟨121,1059654899,1059655721⟩,
⟨128,1117103621,1117104486⟩]
theorem checked11744 : checkPrefixCuts (2^48) 1543241729 9 Manual.Count131072.C011744.packed 128 cuts11744 = true := by
 decide +kernel
def pointBounds11744 : List (Nat × Nat × Nat) := [(1543267328,93039542195721,93039917911278),(1543316480,93039961136377,93040336852260),(1543365632,93040376963203,93040752679404)]
theorem point_links_checked11744 : (cuts11744.take 3).map (fun c => (1543241729-1+2*2^9*c.k,93039317308304+c.lower,93039693023683+c.upper)) = pointBounds11744 := by
 decide +kernel
def cuts11745 : List PrefixCut := [⟨41,359094290,359094575⟩,
⟨89,780183363,780183974⟩,
⟨128,1117920278,1117921155⟩]
theorem checked11745 : checkPrefixCuts (2^48) 1543372801 9 Manual.Count131072.C011745.packed 128 cuts11745 = true := by
 decide +kernel
def pointBounds11745 : List (Nat × Nat × Nat) := [(1543414784,93040793506215,93041169222744),(1543463936,93041214595288,93041590312143)]
theorem point_links_checked11745 : (cuts11745.take 2).map (fun c => (1543372801-1+2*2^9*c.k,93040434411925+c.lower,93040810128169+c.upper)) = pointBounds11745 := by
 decide +kernel
def cuts11746 : List PrefixCut := [⟨9,77320818,77320878⟩,
⟨57,500571427,500571821⟩,
⟨105,927455565,927456288⟩,
⟨128,1126396002,1126396883⟩]
theorem checked11746 : checkPrefixCuts (2^48) 1543503873 9 Manual.Count131072.C011746.packed 128 cuts11746 = true := by
 decide +kernel
def pointBounds11746 : List (Nat × Nat × Nat) := [(1543513088,93041629653021,93042005370202),(1543562240,93042052903630,93042428621145),(1543611392,93042479787768,93042855505612)]
theorem point_links_checked11746 : (cuts11746.take 3).map (fun c => (1543503873-1+2*2^9*c.k,93041552332203+c.lower,93041928049324+c.upper)) = pointBounds11746 := by
 decide +kernel
def cuts11747 : List PrefixCut := [⟨25,225924195,225924368⟩,
⟨73,645669957,645670460⟩,
⟨121,1070142940,1070143773⟩,
⟨128,1132317612,1132318495⟩]
theorem checked11747 : checkPrefixCuts (2^48) 1543634945 9 Manual.Count131072.C011747.packed 128 cuts11747 = true := by
 decide +kernel
def pointBounds11747 : List (Nat × Nat × Nat) := [(1543660544,93042904652400,93043280370575),(1543709696,93043324398162,93043700116667),(1543758848,93043748871145,93044124589980)]
theorem point_links_checked11747 : (cuts11747.take 3).map (fun c => (1543634945-1+2*2^9*c.k,93042678728205+c.lower,93043054446207+c.upper)) = pointBounds11747 := by
 decide +kernel
def cuts11748 : List PrefixCut := [⟨41,358820579,358820859⟩,
⟨89,775061981,775062580⟩,
⟨128,1122740251,1122741115⟩]
theorem checked11748 : checkPrefixCuts (2^48) 1543766017 9 Manual.Count131072.C011748.packed 128 cuts11748 = true := by
 decide +kernel
def pointBounds11748 : List (Nat × Nat × Nat) := [(1543808000,93044169866396,93044545585561),(1543857152,93044586107798,93044961827282)]
theorem point_links_checked11748 : (cuts11748.take 2).map (fun c => (1543766017-1+2*2^9*c.k,93043811045817+c.lower,93044186764702+c.upper)) = pointBounds11748 := by
 decide +kernel
def cuts11749 : List PrefixCut := [⟨9,82223602,82223667⟩,
⟨57,513934844,513935246⟩,
⟨105,936881861,936882586⟩,
⟨128,1141240653,1141241537⟩]
theorem checked11749 : checkPrefixCuts (2^48) 1543897089 9 Manual.Count131072.C011749.packed 128 cuts11749 = true := by
 decide +kernel
def pointBounds11749 : List (Nat × Nat × Nat) := [(1543906304,93045016009670,93045391729484),(1543955456,93045447720912,93045823441063),(1544004608,93045870667929,93046246388403)]
theorem point_links_checked11749 : (cuts11749.take 3).map (fun c => (1543897089-1+2*2^9*c.k,93044933786068+c.lower,93045309505817+c.upper)) = pointBounds11749 := by
 decide +kernel
def cuts11750 : List PrefixCut := [⟨25,224955174,224955345⟩,
⟨73,649698128,649698626⟩,
⟨121,1080260798,1080261629⟩,
⟨128,1140414521,1140415397⟩]
theorem checked11750 : checkPrefixCuts (2^48) 1544028161 9 Manual.Count131072.C011750.packed 128 cuts11750 = true := by
 decide +kernel
def pointBounds11750 : List (Nat × Nat × Nat) := [(1544053760,93046299981895,93046675702699),(1544102912,93046724724849,93047100445980),(1544152064,93047155287519,93047531008983)]
theorem point_links_checked11750 : (cuts11750.take 3).map (fun c => (1544028161-1+2*2^9*c.k,93046075026721+c.lower,93046450747354+c.upper)) = pointBounds11750 := by
 decide +kernel
def cuts11751 : List PrefixCut := [⟨41,346698644,346698915⟩,
⟨89,762651862,762652459⟩,
⟨128,1117532457,1117533330⟩]
theorem checked11751 : checkPrefixCuts (2^48) 1544159233 9 Manual.Count131072.C011751.packed 128 cuts11751 = true := by
 decide +kernel
def pointBounds11751 : List (Nat × Nat × Nat) := [(1544201216,93047562139886,93047937861666),(1544250368,93047978093104,93048353815210)]
theorem point_links_checked11751 : (cuts11751.take 2).map (fun c => (1544159233-1+2*2^9*c.k,93047215441242+c.lower,93047591162751+c.upper)) = pointBounds11751 := by
 decide +kernel
def cuts11752 : List PrefixCut := [⟨9,76734636,76734695⟩,
⟨57,494848445,494848831⟩,
⟨105,918599064,918599777⟩,
⟨128,1119078511,1119079382⟩]
theorem checked11752 : checkPrefixCuts (2^48) 1544290305 9 Manual.Count131072.C011752.packed 128 cuts11752 = true := by
 decide +kernel
def pointBounds11752 : List (Nat × Nat × Nat) := [(1544299520,93048409708335,93048785430776),(1544348672,93048827822144,93049203544912),(1544397824,93049251572763,93049627295858)]
theorem point_links_checked11752 : (cuts11752.take 3).map (fun c => (1544290305-1+2*2^9*c.k,93048332973699+c.lower,93048708696081+c.upper)) = pointBounds11752 := by
 decide +kernel
def cuts11753 : List PrefixCut := [⟨25,217972358,217972528⟩,
⟨73,646798921,646799419⟩,
⟨121,1073424942,1073425770⟩,
⟨128,1136296916,1136297793⟩]
theorem checked11753 : checkPrefixCuts (2^48) 1544421377 9 Manual.Count131072.C011753.packed 128 cuts11753 = true := by
 decide +kernel
def pointBounds11753 : List (Nat × Nat × Nat) := [(1544446976,93049670024568,93050045747991),(1544496128,93050098851131,93050474574882),(1544545280,93050525477152,93050901201233)]
theorem point_links_checked11753 : (cuts11753.take 3).map (fun c => (1544421377-1+2*2^9*c.k,93049452052210+c.lower,93049827775463+c.upper)) = pointBounds11753 := by
 decide +kernel
def cuts11754 : List PrefixCut := [⟨41,364651605,364651887⟩,
⟨89,791068135,791068743⟩,
⟨128,1140209416,1140210295⟩]
theorem checked11754 : checkPrefixCuts (2^48) 1544552449 9 Manual.Count131072.C011754.packed 128 cuts11754 = true := by
 decide +kernel
def pointBounds11754 : List (Nat × Nat × Nat) := [(1544594432,93050953000731,93051328725143),(1544643584,93051379417261,93051755141999)]
theorem point_links_checked11754 : (cuts11754.take 2).map (fun c => (1544552449-1+2*2^9*c.k,93050588349126+c.lower,93050964073256+c.upper)) = pointBounds11754 := by
 decide +kernel
def cuts11755 : List PrefixCut := [⟨9,78355105,78355166⟩,
⟨57,491989297,491989681⟩,
⟨105,921280602,921281315⟩,
⟨128,1120069115,1120069981⟩]
theorem checked11755 : checkPrefixCuts (2^48) 1544683521 9 Manual.Count131072.C011755.packed 128 cuts11755 = true := by
 decide +kernel
def pointBounds11755 : List (Nat × Nat × Nat) := [(1544692736,93051806913647,93052182638717),(1544741888,93052220547839,93052596273232),(1544791040,93052649839144,93053025564866)]
theorem point_links_checked11755 : (cuts11755.take 3).map (fun c => (1544683521-1+2*2^9*c.k,93051728558542+c.lower,93052104283551+c.upper)) = pointBounds11755 := by
 decide +kernel
def cuts11756 : List PrefixCut := [⟨25,219374489,219374660⟩,
⟨73,646269789,646270291⟩,
⟨121,1074973593,1074974432⟩,
⟨128,1135461075,1135461960⟩]
theorem checked11756 : checkPrefixCuts (2^48) 1544814593 9 Manual.Count131072.C011756.packed 128 cuts11756 = true := by
 decide +kernel
def pointBounds11756 : List (Nat × Nat × Nat) := [(1544840192,93053068002146,93053443728192),(1544889344,93053494897446,93053870623823),(1544938496,93053923601250,93054299327964)]
theorem point_links_checked11756 : (cuts11756.take 3).map (fun c => (1544814593-1+2*2^9*c.k,93052848627657+c.lower,93053224353532+c.upper)) = pointBounds11756 := by
 decide +kernel
def cuts11757 : List PrefixCut := [⟨41,364558765,364559046⟩,
⟨89,790502461,790503066⟩,
⟨128,1133543063,1133543939⟩]
theorem checked11757 : checkPrefixCuts (2^48) 1544945665 9 Manual.Count131072.C011757.packed 128 cuts11757 = true := by
 decide +kernel
def pointBounds11757 : List (Nat × Nat × Nat) := [(1544987648,93054348647497,93054724374538),(1545036800,93054774591193,93055150318558)]
theorem point_links_checked11757 : (cuts11757.take 2).map (fun c => (1544945665-1+2*2^9*c.k,93053984088732+c.lower,93054359815492+c.upper)) = pointBounds11757 := by
 decide +kernel
def cuts11758 : List PrefixCut := [⟨9,73780790,73780847⟩,
⟨57,501519119,501519505⟩,
⟨105,919589091,919589800⟩,
⟨128,1121970249,1121971118⟩]
theorem checked11758 : checkPrefixCuts (2^48) 1545076737 9 Manual.Count131072.C011758.packed 128 cuts11758 = true := by
 decide +kernel
def pointBounds11758 : List (Nat × Nat × Nat) := [(1545085952,93055191412585,93055567140278),(1545135104,93055619150914,93055994878936),(1545184256,93056037220886,93056412949231)]
theorem point_links_checked11758 : (cuts11758.take 3).map (fun c => (1545076737-1+2*2^9*c.k,93055117631795+c.lower,93055493359431+c.upper)) = pointBounds11758 := by
 decide +kernel
def cuts11759 : List PrefixCut := [⟨25,220593776,220593947⟩,
⟨73,644101775,644102273⟩,
⟨121,1070692814,1070693642⟩,
⟨128,1134443512,1134444390⟩]
theorem checked11759 : checkPrefixCuts (2^48) 1545207809 9 Manual.Count131072.C011759.packed 128 cuts11759 = true := by
 decide +kernel
def pointBounds11759 : List (Nat × Nat × Nat) := [(1545233408,93056460195820,93056835924496),(1545282560,93056883703819,93057259432822),(1545331712,93057310294858,93057686024191)]
theorem point_links_checked11759 : (cuts11759.take 3).map (fun c => (1545207809-1+2*2^9*c.k,93056239602044+c.lower,93056615330549+c.upper)) = pointBounds11759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000054
