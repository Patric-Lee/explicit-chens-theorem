import PlattAssemblyKernel
import PlattCertificates.Count131072.C012784
import PlattCertificates.Count131072.C012785
import PlattCertificates.Count131072.C012786
import PlattCertificates.Count131072.C012787
import PlattCertificates.Count131072.C012788
import PlattCertificates.Count131072.C012789
import PlattCertificates.Count131072.C012790
import PlattCertificates.Count131072.C012791
import PlattCertificates.Count131072.C012792
import PlattCertificates.Count131072.C012793
import PlattCertificates.Count131072.C012794
import PlattCertificates.Count131072.C012795
import PlattCertificates.Count131072.C012796
import PlattCertificates.Count131072.C012797
import PlattCertificates.Count131072.C012798
import PlattCertificates.Count131072.C012799
import PlattCertificates.Count131072.C012800
import PlattCertificates.Count131072.C012801
import PlattCertificates.Count131072.C012802
import PlattCertificates.Count131072.C012803
import PlattCertificates.Count131072.C012804
import PlattCertificates.Count131072.C012805
import PlattCertificates.Count131072.C012806
import PlattCertificates.Count131072.C012807
import PlattCertificates.Count131072.C012808
import PlattCertificates.Count131072.C012809
import PlattCertificates.Count131072.C012810
import PlattCertificates.Count131072.C012811
import PlattCertificates.Count131072.C012812
import PlattCertificates.Count131072.C012813
import PlattCertificates.Count131072.C012814
import PlattCertificates.Count131072.C012815
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000087
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12784 : List PrefixCut := [⟨38,309532899,309533125⟩,
⟨90,726645157,726645689⟩,
⟨128,1028620123,1028620883⟩]
theorem checked12784 : checkPrefixCuts (2^48) 1679556609 9 Manual.Count131072.C012784.packed 128 cuts12784 = true := by
 decide +kernel
def pointBounds12784 : List (Nat × Nat × Nat) := [(1679595520,94163404589573,94163781153283),(1679648768,94163821701831,94164198265847)]
theorem point_links_checked12784 : (cuts12784.take 2).map (fun c => (1679556609-1+2*2^9*c.k,94163095056674+c.lower,94163471620158+c.upper)) = pointBounds12784 := by
 decide +kernel
def cuts12785 : List PrefixCut := [⟨14,111772515,111772601⟩,
⟨66,522155427,522155813⟩,
⟨118,950119845,950120540⟩,
⟨128,1032728479,1032729235⟩]
theorem checked12785 : checkPrefixCuts (2^48) 1679687681 9 Manual.Count131072.C012785.packed 128 cuts12785 = true := by
 decide +kernel
def pointBounds12785 : List (Nat × Nat × Nat) := [(1679702016,94164235449312,94164612013642),(1679755264,94164645832224,94165022396854),(1679808512,94165073796642,94165450361581)]
theorem point_links_checked12785 : (cuts12785.take 3).map (fun c => (1679687681-1+2*2^9*c.k,94164123676797+c.lower,94164500241041+c.upper)) = pointBounds12785 := by
 decide +kernel
def cuts12786 : List PrefixCut := [⟨42,334283174,334283422⟩,
⟨94,756188448,756189005⟩,
⟨128,1026113577,1026114332⟩]
theorem checked12786 : checkPrefixCuts (2^48) 1679818753 9 Manual.Count131072.C012786.packed 128 cuts12786 = true := by
 decide +kernel
def pointBounds12786 : List (Nat × Nat × Nat) := [(1679861760,94165490688450,94165867253698),(1679915008,94165912593724,94166289159281)]
theorem point_links_checked12786 : (cuts12786.take 2).map (fun c => (1679818753-1+2*2^9*c.k,94165156405276+c.lower,94165532970276+c.upper)) = pointBounds12786 := by
 decide +kernel
def cuts12787 : List PrefixCut := [⟨18,143254115,143254220⟩,
⟨70,572169519,572169942⟩,
⟨122,982474450,982475173⟩,
⟨128,1033238098,1033238858⟩]
theorem checked12787 : checkPrefixCuts (2^48) 1679949825 9 Manual.Count131072.C012787.packed 128 cuts12787 = true := by
 decide +kernel
def pointBounds12787 : List (Nat × Nat × Nat) := [(1679968256,94166325772968,94166702338828),(1680021504,94166754688372,94167131254550),(1680074752,94167164993303,94167541559781)]
theorem point_links_checked12787 : (cuts12787.take 3).map (fun c => (1679949825-1+2*2^9*c.k,94166182518853+c.lower,94166559084608+c.upper)) = pointBounds12787 := by
 decide +kernel
def cuts12788 : List PrefixCut := [⟨46,362711407,362711674⟩,
⟨98,782874481,782875053⟩,
⟨128,1023440330,1023441078⟩]
theorem checked12788 : checkPrefixCuts (2^48) 1680080897 9 Manual.Count131072.C012788.packed 128 cuts12788 = true := by
 decide +kernel
def pointBounds12788 : List (Nat × Nat × Nat) := [(1680128000,94167578468358,94167955035140),(1680181248,94167998631432,94168375198519)]
theorem point_links_checked12788 : (cuts12788.take 2).map (fun c => (1680080897-1+2*2^9*c.k,94167215756951+c.lower,94167592323466+c.upper)) = pointBounds12788 := by
 decide +kernel
def cuts12789 : List PrefixCut := [⟨22,174390709,174390841⟩,
⟨74,594694708,594695149⟩,
⟨126,1008452332,1008453072⟩,
⟨128,1025705911,1025706663⟩]
theorem checked12789 : checkPrefixCuts (2^48) 1680211969 9 Manual.Count131072.C012789.packed 128 cuts12789 = true := by
 decide +kernel
def pointBounds12789 : List (Nat × Nat × Nat) := [(1680234496,94168413587990,94168790155385),(1680287744,94168833891989,94169210459693),(1680340992,94169247649613,94169624217616)]
theorem point_links_checked12789 : (cuts12789.take 3).map (fun c => (1680211969-1+2*2^9*c.k,94168239197281+c.lower,94168615764544+c.upper)) = pointBounds12789 := by
 decide +kernel
def cuts12790 : List PrefixCut := [⟨50,410729121,410729419⟩,
⟨102,828145667,828146269⟩,
⟨128,1042208889,1042209644⟩]
theorem checked12790 : checkPrefixCuts (2^48) 1680343041 9 Manual.Count131072.C012790.packed 128 cuts12790 = true := by
 decide +kernel
def pointBounds12790 : List (Nat × Nat × Nat) := [(1680394240,94169675632313,94170052200626),(1680447488,94170093048859,94170469617476)]
theorem point_links_checked12790 : (cuts12790.take 2).map (fun c => (1680343041-1+2*2^9*c.k,94169264903192+c.lower,94169641471207+c.upper)) = pointBounds12790 := by
 decide +kernel
def cuts12791 : List PrefixCut := [⟨26,205350083,205350232⟩,
⟨78,628937415,628937872⟩,
⟨128,1025043760,1025044507⟩]
theorem checked12791 : checkPrefixCuts (2^48) 1680474113 9 Manual.Count131072.C012791.packed 128 cuts12791 = true := by
 decide +kernel
def pointBounds12791 : List (Nat × Nat × Nat) := [(1680500736,94170512462164,94170889031083),(1680553984,94170936049496,94171312618723)]
theorem point_links_checked12791 : (cuts12791.take 2).map (fun c => (1680474113-1+2*2^9*c.k,94170307112081+c.lower,94170683680851+c.upper)) = pointBounds12791 := by
 decide +kernel
def cuts12792 : List PrefixCut := [⟨2,16748413,16748426⟩,
⟨54,439471428,439471748⟩,
⟨106,863185918,863186546⟩,
⟨128,1034677535,1034678289⟩]
theorem checked12792 : checkPrefixCuts (2^48) 1680605185 9 Manual.Count131072.C012792.packed 128 cuts12792 = true := by
 decide +kernel
def pointBounds12792 : List (Nat × Nat × Nat) := [(1680607232,94171348904254,94171725473784),(1680660480,94171771627269,94172148197106),(1680713728,94172195341759,94172571911904)]
theorem point_links_checked12792 : (cuts12792.take 3).map (fun c => (1680605185-1+2*2^9*c.k,94171332155841+c.lower,94171708725358+c.upper)) = pointBounds12792 := by
 decide +kernel
def cuts12793 : List PrefixCut := [⟨30,240988841,240989019⟩,
⟨82,659150183,659150668⟩,
⟨128,1033256969,1033257730⟩]
theorem checked12793 : checkPrefixCuts (2^48) 1680736257 9 Manual.Count131072.C012793.packed 128 cuts12793 = true := by
 decide +kernel
def pointBounds12793 : List (Nat × Nat × Nat) := [(1680766976,94172607822217,94172984392666),(1680820224,94173025983559,94173402554315)]
theorem point_links_checked12793 : (cuts12793.take 2).map (fun c => (1680736257-1+2*2^9*c.k,94172366833376+c.lower,94172743403647+c.upper)) = pointBounds12793 := by
 decide +kernel
def cuts12794 : List PrefixCut := [⟨6,51577007,51577044⟩,
⟨58,467869813,467870154⟩,
⟨110,888503133,888503785⟩,
⟨128,1035688166,1035688924⟩]
theorem checked12794 : checkPrefixCuts (2^48) 1680867329 9 Manual.Count131072.C012794.packed 128 cuts12794 = true := by
 decide +kernel
def pointBounds12794 : List (Nat × Nat × Nat) := [(1680873472,94173451667352,94173828238421),(1680926720,94173867960158,94174244531531),(1680979968,94174288593478,94174665165162)]
theorem point_links_checked12794 : (cuts12794.take 3).map (fun c => (1680867329-1+2*2^9*c.k,94173400090345+c.lower,94173776661377+c.upper)) = pointBounds12794 := by
 decide +kernel
def cuts12795 : List PrefixCut := [⟨34,267407015,267407212⟩,
⟨86,690357716,690358223⟩,
⟨128,1021040079,1021040830⟩]
theorem checked12795 : checkPrefixCuts (2^48) 1680998401 9 Manual.Count131072.C012795.packed 128 cuts12795 = true := by
 decide +kernel
def pointBounds12795 : List (Nat × Nat × Nat) := [(1681033216,94174703185526,94175079757513),(1681086464,94175126136227,94175502708524)]
theorem point_links_checked12795 : (cuts12795.take 2).map (fun c => (1680998401-1+2*2^9*c.k,94174435778511+c.lower,94174812350301+c.upper)) = pointBounds12795 := by
 decide +kernel
def cuts12796 : List PrefixCut := [⟨10,83213451,83213510⟩,
⟨62,500444874,500445239⟩,
⟨114,930052293,930052968⟩,
⟨128,1048083151,1048083911⟩]
theorem checked12796 : checkPrefixCuts (2^48) 1681129473 9 Manual.Count131072.C012796.packed 128 cuts12796 = true := by
 decide +kernel
def pointBounds12796 : List (Nat × Nat × Nat) := [(1681139712,94175540032041,94175916604641),(1681192960,94175957263464,94176333836370),(1681246208,94176386870883,94176763444099)]
theorem point_links_checked12796 : (cuts12796.take 3).map (fun c => (1681129473-1+2*2^9*c.k,94175456818590+c.lower,94175833391131+c.upper)) = pointBounds12796 := by
 decide +kernel
def cuts12797 : List PrefixCut := [⟨38,307712408,307712633⟩,
⟨90,727415441,727415972⟩,
⟨128,1035445840,1035446598⟩]
theorem checked12797 : checkPrefixCuts (2^48) 1681260545 9 Manual.Count131072.C012797.packed 128 cuts12797 = true := by
 decide +kernel
def pointBounds12797 : List (Nat × Nat × Nat) := [(1681299456,94176812614149,94177189187675),(1681352704,94177232317182,94177608891014)]
theorem point_links_checked12797 : (cuts12797.take 2).map (fun c => (1681260545-1+2*2^9*c.k,94176504901741+c.lower,94176881475042+c.upper)) = pointBounds12797 := by
 decide +kernel
def cuts12798 : List PrefixCut := [⟨14,115509572,115509658⟩,
⟨66,532842283,532842677⟩,
⟨118,957862039,957862741⟩,
⟨128,1040721750,1040722514⟩]
theorem checked12798 : checkPrefixCuts (2^48) 1681391617 9 Manual.Count131072.C012798.packed 128 cuts12798 = true := by
 decide +kernel
def pointBounds12798 : List (Nat × Nat × Nat) := [(1681405952,94177655857153,94178032431298),(1681459200,94178073189864,94178449764317),(1681512448,94178498209620,94178874784381)]
theorem point_links_checked12798 : (cuts12798.take 3).map (fun c => (1681391617-1+2*2^9*c.k,94177540347581+c.lower,94177916921640+c.upper)) = pointBounds12798 := by
 decide +kernel
def cuts12799 : List PrefixCut := [⟨42,330596678,330596924⟩,
⟨94,750400577,750401129⟩,
⟨128,1035451376,1035452132⟩]
theorem checked12799 : checkPrefixCuts (2^48) 1681522689 9 Manual.Count131072.C012799.packed 128 cuts12799 = true := by
 decide +kernel
def pointBounds12799 : List (Nat × Nat × Nat) := [(1681565696,94178911666009,94179288241078),(1681618944,94179331469908,94179708045283)]
theorem point_links_checked12799 : (cuts12799.take 2).map (fun c => (1681522689-1+2*2^9*c.k,94178581069331+c.lower,94178957644154+c.upper)) = pointBounds12799 := by
 decide +kernel
def cuts12800 : List PrefixCut := [⟨18,144782732,144782837⟩,
⟨70,560710286,560710691⟩,
⟨122,980641497,980642210⟩,
⟨128,1025997969,1025998716⟩]
theorem checked12800 : checkPrefixCuts (2^48) 1681653761 9 Manual.Count131072.C012800.packed 128 cuts12800 = true := by
 decide +kernel
def pointBounds12800 : List (Nat × Nat × Nat) := [(1681672192,94179761303439,94180137879123),(1681725440,94180177230993,94180553806977),(1681778688,94180597162204,94180973738496)]
theorem point_links_checked12800 : (cuts12800.take 3).map (fun c => (1681653761-1+2*2^9*c.k,94179616520707+c.lower,94179993096286+c.upper)) = pointBounds12800 := by
 decide +kernel
def cuts12801 : List PrefixCut := [⟨46,366528111,366528387⟩,
⟨98,792457894,792458490⟩,
⟨128,1037465995,1037466770⟩]
theorem checked12801 : checkPrefixCuts (2^48) 1681784833 9 Manual.Count131072.C012801.packed 128 cuts12801 = true := by
 decide +kernel
def pointBounds12801 : List (Nat × Nat × Nat) := [(1681831936,94181009046787,94181385623389),(1681885184,94181434976570,94181811553492)]
theorem point_links_checked12801 : (cuts12801.take 2).map (fun c => (1681784833-1+2*2^9*c.k,94180642518676+c.lower,94181019095002+c.upper)) = pointBounds12801 := by
 decide +kernel
def cuts12802 : List PrefixCut := [⟨22,180406079,180406208⟩,
⟨74,609321103,609321546⟩,
⟨126,1024500380,1024501129⟩,
⟨128,1040397754,1040398515⟩]
theorem checked12802 : checkPrefixCuts (2^48) 1681915905 9 Manual.Count131072.C012802.packed 128 cuts12802 = true := by
 decide +kernel
def pointBounds12802 : List (Nat × Nat × Nat) := [(1681938432,94181860390750,94182236967980),(1681991680,94182289305774,94182665883318),(1682044928,94182704485051,94183081062901)]
theorem point_links_checked12802 : (cuts12802.take 3).map (fun c => (1681915905-1+2*2^9*c.k,94181679984671+c.lower,94182056561772+c.upper)) = pointBounds12802 := by
 decide +kernel
def cuts12803 : List PrefixCut := [⟨50,404623558,404623857⟩,
⟨102,822621141,822621753⟩,
⟨128,1033455619,1033456384⟩]
theorem checked12803 : checkPrefixCuts (2^48) 1682046977 9 Manual.Count131072.C012803.packed 128 cuts12803 = true := by
 decide +kernel
def pointBounds12803 : List (Nat × Nat × Nat) := [(1682098176,94183125005983,94183501584144),(1682151424,94183543003566,94183919582040)]
theorem point_links_checked12803 : (cuts12803.take 2).map (fun c => (1682046977-1+2*2^9*c.k,94182720382425+c.lower,94183096960287+c.upper)) = pointBounds12803 := by
 decide +kernel
def cuts12804 : List PrefixCut := [⟨26,202632114,202632265⟩,
⟨78,624786281,624786741⟩,
⟨128,1017479616,1017480366⟩]
theorem checked12804 : checkPrefixCuts (2^48) 1682178049 9 Manual.Count131072.C012804.packed 128 cuts12804 = true := by
 decide +kernel
def pointBounds12804 : List (Nat × Nat × Nat) := [(1682204672,94183956470158,94184333048936),(1682257920,94184378624325,94184755203412)]
theorem point_links_checked12804 : (cuts12804.take 2).map (fun c => (1682178049-1+2*2^9*c.k,94183753838044+c.lower,94184130416671+c.upper)) = pointBounds12804 := by
 decide +kernel
def cuts12805 : List PrefixCut := [⟨2,16564136,16564148⟩,
⟨54,425975979,425976295⟩,
⟨106,846417019,846417641⟩,
⟨128,1019742590,1019743340⟩]
theorem checked12805 : checkPrefixCuts (2^48) 1682309121 9 Manual.Count131072.C012805.packed 128 cuts12805 = true := by
 decide +kernel
def pointBounds12805 : List (Nat × Nat × Nat) := [(1682311168,94184787881796,94185164461185),(1682364416,94185197293639,94185573873332),(1682417664,94185617734679,94185994314678)]
theorem point_links_checked12805 : (cuts12805.take 3).map (fun c => (1682309121-1+2*2^9*c.k,94184771317660+c.lower,94185147897037+c.upper)) = pointBounds12805 := by
 decide +kernel
def cuts12806 : List PrefixCut := [⟨30,246265663,246265843⟩,
⟨82,661661205,661661685⟩,
⟨128,1035389046,1035389793⟩]
theorem checked12806 : checkPrefixCuts (2^48) 1682440193 9 Manual.Count131072.C012806.packed 128 cuts12806 = true := by
 decide +kernel
def pointBounds12806 : List (Nat × Nat × Nat) := [(1682470912,94186037325913,94186413906220),(1682524160,94186452721455,94186829302062)]
theorem point_links_checked12806 : (cuts12806.take 2).map (fun c => (1682440193-1+2*2^9*c.k,94185791060250+c.lower,94186167640377+c.upper)) = pointBounds12806 := by
 decide +kernel
def cuts12807 : List PrefixCut := [⟨6,49851892,49851927⟩,
⟨58,471243596,471243944⟩,
⟨110,889778067,889778722⟩,
⟨128,1035141245,1035142007⟩]
theorem checked12807 : checkPrefixCuts (2^48) 1682571265 9 Manual.Count131072.C012807.packed 128 cuts12807 = true := by
 decide +kernel
def pointBounds12807 : List (Nat × Nat × Nat) := [(1682577408,94186876301188,94187252882097),(1682630656,94187297692892,94187674274114),(1682683904,94187716227363,94188092808892)]
theorem point_links_checked12807 : (cuts12807.take 3).map (fun c => (1682571265-1+2*2^9*c.k,94186826449296+c.lower,94187203030170+c.upper)) = pointBounds12807 := by
 decide +kernel
def cuts12808 : List PrefixCut := [⟨34,267805256,267805453⟩,
⟨86,685644192,685644694⟩,
⟨128,1026696746,1026697499⟩]
theorem checked12808 : checkPrefixCuts (2^48) 1682702337 9 Manual.Count131072.C012808.packed 128 cuts12808 = true := by
 decide +kernel
def pointBounds12808 : List (Nat × Nat × Nat) := [(1682737152,94188129395797,94188505977630),(1682790400,94188547234733,94188923816871)]
theorem point_links_checked12808 : (cuts12808.take 2).map (fun c => (1682702337-1+2*2^9*c.k,94187861590541+c.lower,94188238172177+c.upper)) = pointBounds12808 := by
 decide +kernel
def cuts12809 : List PrefixCut := [⟨10,75267877,75267934⟩,
⟨62,497763659,497764027⟩,
⟨114,923925648,923926325⟩,
⟨128,1044345765,1044346531⟩]
theorem checked12809 : checkPrefixCuts (2^48) 1682833409 9 Manual.Count131072.C012809.packed 128 cuts12809 = true := by
 decide +kernel
def pointBounds12809 : List (Nat × Nat × Nat) := [(1682843648,94188963555164,94189340137610),(1682896896,94189386050946,94189762633703),(1682950144,94189812212935,94190188796001)]
theorem point_links_checked12809 : (cuts12809.take 3).map (fun c => (1682833409-1+2*2^9*c.k,94188888287287+c.lower,94189264869676+c.upper)) = pointBounds12809 := by
 decide +kernel
def cuts12810 : List PrefixCut := [⟨38,300878260,300878482⟩,
⟨90,711459635,711460162⟩,
⟨128,1018007588,1018008337⟩]
theorem checked12810 : checkPrefixCuts (2^48) 1682964481 9 Manual.Count131072.C012810.packed 128 cuts12810 = true := by
 decide +kernel
def pointBounds12810 : List (Nat × Nat × Nat) := [(1683003392,94190233511312,94190610094689),(1683056640,94190644092687,94191020676369)]
theorem point_links_checked12810 : (cuts12810.take 2).map (fun c => (1682964481-1+2*2^9*c.k,94189932633052+c.lower,94190309216207+c.upper)) = pointBounds12810 := by
 decide +kernel
def cuts12811 : List PrefixCut := [⟨14,112884104,112884187⟩,
⟨66,529292620,529293009⟩,
⟨118,951540968,951541664⟩,
⟨128,1033982348,1033983106⟩]
theorem checked12811 : checkPrefixCuts (2^48) 1683095553 9 Manual.Count131072.C012811.packed 128 cuts12811 = true := by
 decide +kernel
def pointBounds12811 : List (Nat × Nat × Nat) := [(1683109888,94191063524744,94191440108731),(1683163136,94191479933260,94191856517553),(1683216384,94191902181608,94192278766208)]
theorem point_links_checked12811 : (cuts12811.take 3).map (fun c => (1683095553-1+2*2^9*c.k,94190950640640+c.lower,94191327224544+c.upper)) = pointBounds12811 := by
 decide +kernel
def cuts12812 : List PrefixCut := [⟨42,342803628,342803879⟩,
⟨94,755326708,755327263⟩,
⟨128,1028216841,1028217601⟩]
theorem checked12812 : checkPrefixCuts (2^48) 1683226625 9 Manual.Count131072.C012812.packed 128 cuts12812 = true := by
 decide +kernel
def pointBounds12812 : List (Nat × Nat × Nat) := [(1683269632,94192327426616,94192704011529),(1683322880,94192739949696,94193116534913)]
theorem point_links_checked12812 : (cuts12812.take 2).map (fun c => (1683226625-1+2*2^9*c.k,94191984622988+c.lower,94192361207650+c.upper)) = pointBounds12812 := by
 decide +kernel
def cuts12813 : List PrefixCut := [⟨18,142796883,142796988⟩,
⟨70,566998310,566998728⟩,
⟨122,989848617,989849341⟩,
⟨128,1039171928,1039172689⟩]
theorem checked12813 : checkPrefixCuts (2^48) 1683357697 9 Manual.Count131072.C012813.packed 128 cuts12813 = true := by
 decide +kernel
def pointBounds12813 : List (Nat × Nat × Nat) := [(1683376128,94193155636712,94193532222239),(1683429376,94193579838139,94193956423979),(1683482624,94194002688446,94194379274592)]
theorem point_links_checked12813 : (cuts12813.take 3).map (fun c => (1683357697-1+2*2^9*c.k,94193012839829+c.lower,94193389425251+c.upper)) = pointBounds12813 := by
 decide +kernel
def cuts12814 : List PrefixCut := [⟨46,383378096,383378377⟩,
⟨98,799179734,799180320⟩,
⟨128,1039593020,1039593782⟩]
theorem checked12814 : checkPrefixCuts (2^48) 1683488769 9 Manual.Count131072.C012814.packed 128 cuts12814 = true := by
 decide +kernel
def pointBounds12814 : List (Nat × Nat × Nat) := [(1683535872,94194435389853,94194811976317),(1683589120,94194851191491,94195227778260)]
theorem point_links_checked12814 : (cuts12814.take 2).map (fun c => (1683488769-1+2*2^9*c.k,94194052011757+c.lower,94194428597940+c.upper)) = pointBounds12814 := by
 decide +kernel
def cuts12815 : List PrefixCut := [⟨22,173536208,173536336⟩,
⟨74,597503273,597503710⟩,
⟨126,1014769963,1014770708⟩,
⟨128,1031654277,1031655034⟩]
theorem checked12815 : checkPrefixCuts (2^48) 1683619841 9 Manual.Count131072.C012815.packed 128 cuts12815 = true := by
 decide +kernel
def pointBounds12815 : List (Nat × Nat × Nat) := [(1683642368,94195265140985,94195641728058),(1683695616,94195689108050,94196065695432),(1683748864,94196106374740,94196482962430)]
theorem point_links_checked12815 : (cuts12815.take 3).map (fun c => (1683619841-1+2*2^9*c.k,94195091604777+c.lower,94195468191722+c.upper)) = pointBounds12815 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000087
