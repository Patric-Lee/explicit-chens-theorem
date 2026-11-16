import PlattAssemblyKernel
import PlattCertificates.Count131072.C015696
import PlattCertificates.Count131072.C015697
import PlattCertificates.Count131072.C015698
import PlattCertificates.Count131072.C015699
import PlattCertificates.Count131072.C015700
import PlattCertificates.Count131072.C015701
import PlattCertificates.Count131072.C015702
import PlattCertificates.Count131072.C015703
import PlattCertificates.Count131072.C015704
import PlattCertificates.Count131072.C015705
import PlattCertificates.Count131072.C015706
import PlattCertificates.Count131072.C015707
import PlattCertificates.Count131072.C015708
import PlattCertificates.Count131072.C015709
import PlattCertificates.Count131072.C015710
import PlattCertificates.Count131072.C015711
import PlattCertificates.Count131072.C015712
import PlattCertificates.Count131072.C015713
import PlattCertificates.Count131072.C015714
import PlattCertificates.Count131072.C015715
import PlattCertificates.Count131072.C015716
import PlattCertificates.Count131072.C015717
import PlattCertificates.Count131072.C015718
import PlattCertificates.Count131072.C015719
import PlattCertificates.Count131072.C015720
import PlattCertificates.Count131072.C015721
import PlattCertificates.Count131072.C015722
import PlattCertificates.Count131072.C015723
import PlattCertificates.Count131072.C015724
import PlattCertificates.Count131072.C015725
import PlattCertificates.Count131072.C015726
import PlattCertificates.Count131072.C015727
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000178
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15696 : List PrefixCut := [⟨23,149937880,149937981⟩,
⟨86,558366405,558366774⟩,
⟨128,830508460,830509005⟩]
theorem checked15696 : checkPrefixCuts (2^48) 2061238273 9 Manual.Count131072.C015696.packed 128 cuts15696 = true := by
 decide +kernel
def pointBounds15696 : List (Nat × Nat × Nat) := [(2061261824,96863685635728,96864064061215),(2061326336,96864094064253,96864472490008)]
theorem point_links_checked15696 : (cuts15696.take 2).map (fun c => (2061238273-1+2*2^9*c.k,96863535697848+c.lower,96863914123234+c.upper)) = pointBounds15696 := by
 decide +kernel
def cuts15697 : List PrefixCut := [⟨21,139960482,139960574⟩,
⟨84,553005902,553006268⟩,
⟨128,837556012,837556566⟩]
theorem checked15697 : checkPrefixCuts (2^48) 2061369345 9 Manual.Count131072.C015697.packed 128 cuts15697 = true := by
 decide +kernel
def pointBounds15697 : List (Nat × Nat × Nat) := [(2061390848,96864506166790,96864884592813),(2061455360,96864919212210,96865297638507)]
theorem point_links_checked15697 : (cuts15697.take 2).map (fun c => (2061369345-1+2*2^9*c.k,96864366206308+c.lower,96864744632239+c.upper)) = pointBounds15697 := by
 decide +kernel
def cuts15698 : List PrefixCut := [⟨19,131076674,131076755⟩,
⟨82,541229134,541229489⟩,
⟨128,830676371,830676912⟩]
theorem checked15698 : checkPrefixCuts (2^48) 2061500417 9 Manual.Count131072.C015698.packed 128 cuts15698 = true := by
 decide +kernel
def pointBounds15698 : List (Nat × Nat × Nat) := [(2061519872,96865334838994,96865713265560),(2061584384,96865744991454,96866123418294)]
theorem point_links_checked15698 : (cuts15698.take 2).map (fun c => (2061500417-1+2*2^9*c.k,96865203762320+c.lower,96865582188805+c.upper)) = pointBounds15698 := by
 decide +kernel
def cuts15699 : List PrefixCut := [⟨17,110998551,110998623⟩,
⟨80,513479819,513480154⟩,
⟨128,823250715,823251251⟩]
theorem checked15699 : checkPrefixCuts (2^48) 2061631489 9 Manual.Count131072.C015699.packed 128 cuts15699 = true := by
 decide +kernel
def pointBounds15699 : List (Nat × Nat × Nat) := [(2061648896,96866145437242,96866523864340),(2061713408,96866547918510,96866926345871)]
theorem point_links_checked15699 : (cuts15699.take 2).map (fun c => (2061631489-1+2*2^9*c.k,96866034438691+c.lower,96866412865717+c.upper)) = pointBounds15699 := by
 decide +kernel
def cuts15700 : List PrefixCut := [⟨15,97066415,97066479⟩,
⟨78,513174229,513174568⟩,
⟨128,835211957,835212506⟩]
theorem checked15700 : checkPrefixCuts (2^48) 2061762561 9 Manual.Count131072.C015700.packed 128 cuts15700 = true := by
 decide +kernel
def pointBounds15700 : List (Nat × Nat × Nat) := [(2061777920,96866954755821,96867333183447),(2061842432,96867370863635,96867749291536)]
theorem point_links_checked15700 : (cuts15700.take 2).map (fun c => (2061762561-1+2*2^9*c.k,96866857689406+c.lower,96867236116968+c.upper)) = pointBounds15700 := by
 decide +kernel
def cuts15701 : List PrefixCut := [⟨13,86002789,86002848⟩,
⟨76,495395597,495395919⟩,
⟨128,835158700,835159239⟩]
theorem checked15701 : checkPrefixCuts (2^48) 2061893633 9 Manual.Count131072.C015701.packed 128 cuts15701 = true := by
 decide +kernel
def pointBounds15701 : List (Nat × Nat × Nat) := [(2061906944,96867778904152,96868157332322),(2061971456,96868188296960,96868566725393)]
theorem point_links_checked15701 : (cuts15701.take 2).map (fun c => (2061893633-1+2*2^9*c.k,96867692901363+c.lower,96868071329474+c.upper)) = pointBounds15701 := by
 decide +kernel
def cuts15702 : List PrefixCut := [⟨11,76032593,76032640⟩,
⟨74,488402832,488403145⟩,
⟨128,844524306,844524845⟩]
theorem checked15702 : checkPrefixCuts (2^48) 2062024705 9 Manual.Count131072.C015702.packed 128 cuts15702 = true := by
 decide +kernel
def pointBounds15702 : List (Nat × Nat × Nat) := [(2062035968,96868604092656,96868982521353),(2062100480,96869016462895,96869394891858)]
theorem point_links_checked15702 : (cuts15702.take 2).map (fun c => (2062024705-1+2*2^9*c.k,96868528060063+c.lower,96868906488713+c.upper)) = pointBounds15702 := by
 decide +kernel
def cuts15703 : List PrefixCut := [⟨9,58419917,58419954⟩,
⟨72,469126488,469126791⟩,
⟨128,836144550,836145092⟩]
theorem checked15703 : checkPrefixCuts (2^48) 2062155777 9 Manual.Count131072.C015703.packed 128 cuts15703 = true := by
 decide +kernel
def pointBounds15703 : List (Nat × Nat × Nat) := [(2062164992,96869431004286,96869809433512),(2062229504,96869841710857,96870220140349)]
theorem point_links_checked15703 : (cuts15703.take 2).map (fun c => (2062155777-1+2*2^9*c.k,96869372584369+c.lower,96869751013558+c.upper)) = pointBounds15703 := by
 decide +kernel
def cuts15704 : List PrefixCut := [⟨7,47087856,47087887⟩,
⟨70,446031019,446031312⟩,
⟨128,824217273,824217810⟩]
theorem checked15704 : checkPrefixCuts (2^48) 2062286849 9 Manual.Count131072.C015704.packed 128 cuts15704 = true := by
 decide +kernel
def pointBounds15704 : List (Nat × Nat × Nat) := [(2062294016,96870255816775,96870634246537),(2062358528,96870654759938,96871033189962)]
theorem point_links_checked15704 : (cuts15704.take 2).map (fun c => (2062286849-1+2*2^9*c.k,96870208728919+c.lower,96870587158650+c.upper)) = pointBounds15704 := by
 decide +kernel
def cuts15705 : List PrefixCut := [⟨5,33573573,33573594⟩,
⟨68,444774673,444774959⟩,
⟨128,840405528,840406071⟩]
theorem checked15705 : checkPrefixCuts (2^48) 2062417921 9 Manual.Count131072.C015705.packed 128 cuts15705 = true := by
 decide +kernel
def pointBounds15705 : List (Nat × Nat × Nat) := [(2062423040,96871066519765,96871444950054),(2062487552,96871477720865,96871856151419)]
theorem point_links_checked15705 : (cuts15705.take 2).map (fun c => (2062417921-1+2*2^9*c.k,96871032946192+c.lower,96871411376460+c.upper)) = pointBounds15705 := by
 decide +kernel
def cuts15706 : List PrefixCut := [⟨3,18013950,18013962⟩,
⟨66,424412942,424413219⟩,
⟨128,823020966,823021503⟩]
theorem checked15706 : checkPrefixCuts (2^48) 2062548993 9 Manual.Count131072.C015706.packed 128 cuts15706 = true := by
 decide +kernel
def pointBounds15706 : List (Nat × Nat × Nat) := [(2062552064,96871891365670,96872269796493),(2062616576,96872297764662,96872676195750)]
theorem point_links_checked15706 : (cuts15706.take 2).map (fun c => (2062548993-1+2*2^9*c.k,96871873351720+c.lower,96872251782531+c.upper)) = pointBounds15706 := by
 decide +kernel
def cuts15707 : List PrefixCut := [⟨1,8187644,8187649⟩,
⟨64,417563355,417563627⟩,
⟨127,839889332,839889876⟩,
⟨128,847394199,847394747⟩]
theorem checked15707 : checkPrefixCuts (2^48) 2062680065 9 Manual.Count131072.C015707.packed 128 cuts15707 = true := by
 decide +kernel
def pointBounds15707 : List (Nat × Nat × Nat) := [(2062681088,96872704560330,96873082991683),(2062745600,96873113936041,96873492367661),(2062810112,96873536262018,96873914693910)]
theorem point_links_checked15707 : (cuts15707.take 3).map (fun c => (2062680065-1+2*2^9*c.k,96872696372686+c.lower,96873074804034+c.upper)) = pointBounds15707 := by
 decide +kernel
def cuts15708 : List PrefixCut := [⟨62,404983600,404983866⟩,
⟨125,813775139,813775678⟩,
⟨128,832604345,832604896⟩]
theorem checked15708 : checkPrefixCuts (2^48) 2062811137 9 Manual.Count131072.C015708.packed 128 cuts15708 = true := by
 decide +kernel
def pointBounds15708 : List (Nat × Nat × Nat) := [(2062874624,96873948750485,96874327182647),(2062939136,96874357542024,96874735974459)]
theorem point_links_checked15708 : (cuts15708.take 2).map (fun c => (2062811137-1+2*2^9*c.k,96873543766885+c.lower,96873922198781+c.upper)) = pointBounds15708 := by
 decide +kernel
def cuts15709 : List PrefixCut := [⟨60,385992662,385992911⟩,
⟨123,797623791,797624304⟩,
⟨128,830231737,830232271⟩]
theorem checked15709 : checkPrefixCuts (2^48) 2062942209 9 Manual.Count131072.C015709.packed 128 cuts15709 = true := by
 decide +kernel
def pointBounds15709 : List (Nat × Nat × Nat) := [(2063003648,96874762363892,96875140796588),(2063068160,96875173995021,96875552427981)]
theorem point_links_checked15709 : (cuts15709.take 2).map (fun c => (2062942209-1+2*2^9*c.k,96874376371230+c.lower,96874754803677+c.upper)) = pointBounds15709 := by
 decide +kernel
def cuts15710 : List PrefixCut := [⟨58,383376112,383376358⟩,
⟨121,784340075,784340582⟩,
⟨128,832634992,832635531⟩]
theorem checked15710 : checkPrefixCuts (2^48) 2063073281 9 Manual.Count131072.C015710.packed 128 cuts15710 = true := by
 decide +kernel
def pointBounds15710 : List (Nat × Nat × Nat) := [(2063132672,96875589979079,96875968412306),(2063197184,96875990943042,96876369376530)]
theorem point_links_checked15710 : (cuts15710.take 2).map (fun c => (2063073281-1+2*2^9*c.k,96875206602967+c.lower,96875585035948+c.upper)) = pointBounds15710 := by
 decide +kernel
def cuts15711 : List PrefixCut := [⟨56,376530725,376530973⟩,
⟨119,779106583,779107093⟩,
⟨128,838584708,838585255⟩]
theorem checked15711 : checkPrefixCuts (2^48) 2063204353 9 Manual.Count131072.C015711.packed 128 cuts15711 = true := by
 decide +kernel
def pointBounds15711 : List (Nat × Nat × Nat) := [(2063261696,96876415768684,96876794202452),(2063326208,96876818344542,96877196778572)]
theorem point_links_checked15711 : (cuts15711.take 2).map (fun c => (2063204353-1+2*2^9*c.k,96876039237959+c.lower,96876417671479+c.upper)) = pointBounds15711 := by
 decide +kernel
def cuts15712 : List PrefixCut := [⟨54,349223863,349224089⟩,
⟨117,759959260,759959753⟩,
⟨128,830892000,830892539⟩]
theorem checked15712 : checkPrefixCuts (2^48) 2063335425 9 Manual.Count131072.C015712.packed 128 cuts15712 = true := by
 decide +kernel
def pointBounds15712 : List (Nat × Nat × Nat) := [(2063390720,96877227046530,96877605480823),(2063455232,96877637781927,96878016216487)]
theorem point_links_checked15712 : (cuts15712.take 2).map (fun c => (2063335425-1+2*2^9*c.k,96876877822667+c.lower,96877256256734+c.upper)) = pointBounds15712 := by
 decide +kernel
def cuts15713 : List PrefixCut := [⟨52,335152005,335152224⟩,
⟨115,743406468,743406951⟩,
⟨128,829202392,829202929⟩]
theorem checked15713 : checkPrefixCuts (2^48) 2063466497 9 Manual.Count131072.C015713.packed 128 cuts15713 = true := by
 decide +kernel
def pointBounds15713 : List (Nat × Nat × Nat) := [(2063519744,96878043866672,96878422301497),(2063584256,96878452121135,96878830556224)]
theorem point_links_checked15713 : (cuts15713.take 2).map (fun c => (2063466497-1+2*2^9*c.k,96877708714667+c.lower,96878087149273+c.upper)) = pointBounds15713 := by
 decide +kernel
def cuts15714 : List PrefixCut := [⟨50,331857325,331857538⟩,
⟨113,742268631,742269111⟩,
⟨128,842653088,842653633⟩]
theorem checked15714 : checkPrefixCuts (2^48) 2063597569 9 Manual.Count131072.C015714.packed 128 cuts15714 = true := by
 decide +kernel
def pointBounds15714 : List (Nat × Nat × Nat) := [(2063648768,96878869774384,96879248209740),(2063713280,96879280185690,96879658621313)]
theorem point_links_checked15714 : (cuts15714.take 2).map (fun c => (2063597569-1+2*2^9*c.k,96878537917059+c.lower,96878916352202+c.upper)) = pointBounds15714 := by
 decide +kernel
def cuts15715 : List PrefixCut := [⟨48,305922294,305922495⟩,
⟨111,723945474,723945947⟩,
⟨128,837689189,837689737⟩]
theorem checked15715 : checkPrefixCuts (2^48) 2063728641 9 Manual.Count131072.C015715.packed 128 cuts15715 = true := by
 decide +kernel
def pointBounds15715 : List (Nat × Nat × Nat) := [(2063777792,96879686492441,96880064928330),(2063842304,96880104515621,96880482951782)]
theorem point_links_checked15715 : (cuts15715.take 2).map (fun c => (2063728641-1+2*2^9*c.k,96879380570147+c.lower,96879759005835+c.upper)) = pointBounds15715 := by
 decide +kernel
def cuts15716 : List PrefixCut := [⟨46,303720958,303721156⟩,
⟨109,726900425,726900890⟩,
⟨128,850592303,850592851⟩]
theorem checked15716 : checkPrefixCuts (2^48) 2063859713 9 Manual.Count131072.C015716.packed 128 cuts15716 = true := by
 decide +kernel
def pointBounds15716 : List (Nat × Nat × Nat) := [(2063906816,96880521980294,96880900416728),(2063971328,96880945159761,96881323596462)]
theorem point_links_checked15716 : (cuts15716.take 2).map (fun c => (2063859713-1+2*2^9*c.k,96880218259336+c.lower,96880596695572+c.upper)) = pointBounds15716 := by
 decide +kernel
def cuts15717 : List PrefixCut := [⟨44,284746053,284746242⟩,
⟨107,693716568,693717025⟩,
⟨128,828446324,828446867⟩]
theorem checked15717 : checkPrefixCuts (2^48) 2063990785 9 Manual.Count131072.C015717.packed 128 cuts15717 = true := by
 decide +kernel
def pointBounds15717 : List (Nat × Nat × Nat) := [(2064035840,96881353597692,96881732034665),(2064100352,96881762568207,96882141005448)]
theorem point_links_checked15717 : (cuts15717.take 2).map (fun c => (2063990785-1+2*2^9*c.k,96881068851639+c.lower,96881447288423+c.upper)) = pointBounds15717 := by
 decide +kernel
def cuts15718 : List PrefixCut := [⟨42,271637080,271637261⟩,
⟨105,685081988,685082437⟩,
⟨128,828666480,828667022⟩]
theorem checked15718 : checkPrefixCuts (2^48) 2064121857 9 Manual.Count131072.C015718.packed 128 cuts15718 = true := by
 decide +kernel
def pointBounds15718 : List (Nat × Nat × Nat) := [(2064164864,96882168935043,96882547372551),(2064229376,96882582379951,96882960817727)]
theorem point_links_checked15718 : (cuts15718.take 2).map (fun c => (2064121857-1+2*2^9*c.k,96881897297963+c.lower,96882275735290+c.upper)) = pointBounds15718 := by
 decide +kernel
def cuts15719 : List PrefixCut := [⟨40,261938776,261938945⟩,
⟨103,674539776,674540215⟩,
⟨128,841703620,841704165⟩]
theorem checked15719 : checkPrefixCuts (2^48) 2064252929 9 Manual.Count131072.C015719.packed 128 cuts15719 = true := by
 decide +kernel
def pointBounds15719 : List (Nat × Nat × Nat) := [(2064293888,96882987903219,96883366341257),(2064358400,96883400504219,96883778942527)]
theorem point_links_checked15719 : (cuts15719.take 2).map (fun c => (2064252929-1+2*2^9*c.k,96882725964443+c.lower,96883104402312+c.upper)) = pointBounds15719 := by
 decide +kernel
def cuts15720 : List PrefixCut := [⟨38,251150859,251151021⟩,
⟨102,665771111,665771547⟩,
⟨128,839332387,839332932⟩]
theorem checked15720 : checkPrefixCuts (2^48) 2064384001 9 Manual.Count131072.C015720.packed 128 cuts15720 = true := by
 decide +kernel
def pointBounds15720 : List (Nat × Nat × Nat) := [(2064422912,96883818818922,96884197257498),(2064488448,96884233439174,96884611878024)]
theorem point_links_checked15720 : (cuts15720.take 2).map (fun c => (2064384001-1+2*2^9*c.k,96883567668063+c.lower,96883946106477+c.upper)) = pointBounds15720 := by
 decide +kernel
def cuts15721 : List PrefixCut := [⟨38,245954043,245954204⟩,
⟨102,657412243,657412674⟩,
⟨128,827554190,827554731⟩]
theorem checked15721 : checkPrefixCuts (2^48) 2064515073 9 Manual.Count131072.C015721.packed 128 cuts15721 = true := by
 decide +kernel
def pointBounds15721 : List (Nat × Nat × Nat) := [(2064553984,96884652954493,96885031393613),(2064619520,96885064412693,96885442852083)]
theorem point_links_checked15721 : (cuts15721.take 2).map (fun c => (2064515073-1+2*2^9*c.k,96884407000450+c.lower,96884785439409+c.upper)) = pointBounds15721 := by
 decide +kernel
def cuts15722 : List PrefixCut := [⟨38,249619379,249619537⟩,
⟨102,667731570,667731999⟩,
⟨128,836226861,836227404⟩]
theorem checked15722 : checkPrefixCuts (2^48) 2064646145 9 Manual.Count131072.C015722.packed 128 cuts15722 = true := by
 decide +kernel
def pointBounds15722 : List (Nat × Nat × Nat) := [(2064685056,96885484174019,96885862613677),(2064750592,96885902286210,96886280726139)]
theorem point_links_checked15722 : (cuts15722.take 2).map (fun c => (2064646145-1+2*2^9*c.k,96885234554640+c.lower,96885612994140+c.upper)) = pointBounds15722 := by
 decide +kernel
def cuts15723 : List PrefixCut := [⟨38,253556809,253556971⟩,
⟨102,675322914,675323347⟩,
⟨128,844489031,844489574⟩]
theorem checked15723 : checkPrefixCuts (2^48) 2064777217 9 Manual.Count131072.C015723.packed 128 cuts15723 = true := by
 decide +kernel
def pointBounds15723 : List (Nat × Nat × Nat) := [(2064816128,96886324338310,96886702778515),(2064881664,96886746104415,96887124544891)]
theorem point_links_checked15723 : (cuts15723.take 2).map (fun c => (2064777217-1+2*2^9*c.k,96886070781501+c.lower,96886449221544+c.upper)) = pointBounds15723 := by
 decide +kernel
def cuts15724 : List PrefixCut := [⟨38,241136328,241136487⟩,
⟨102,661921476,661921903⟩,
⟨128,828214454,828214991⟩]
theorem checked15724 : checkPrefixCuts (2^48) 2064908289 9 Manual.Count131072.C015724.packed 128 cuts15724 = true := by
 decide +kernel
def pointBounds15724 : List (Nat × Nat × Nat) := [(2064947200,96887156406860,96887534847605),(2065012736,96887577192008,96887955633021)]
theorem point_links_checked15724 : (cuts15724.take 2).map (fun c => (2064908289-1+2*2^9*c.k,96886915270532+c.lower,96887293711118+c.upper)) = pointBounds15724 := by
 decide +kernel
def cuts15725 : List PrefixCut := [⟨38,250253365,250253529⟩,
⟨102,665559852,665560281⟩,
⟨128,831297104,831297638⟩]
theorem checked15725 : checkPrefixCuts (2^48) 2065039361 9 Manual.Count131072.C015725.packed 128 cuts15725 = true := by
 decide +kernel
def pointBounds15725 : List (Nat × Nat × Nat) := [(2065078272,96887993738351,96888372179638),(2065143808,96888409044838,96888787486390)]
theorem point_links_checked15725 : (cuts15725.take 2).map (fun c => (2065039361-1+2*2^9*c.k,96887743484986+c.lower,96888121926109+c.upper)) = pointBounds15725 := by
 decide +kernel
def cuts15726 : List PrefixCut := [⟨38,246557484,246557640⟩,
⟨102,661837550,661837975⟩,
⟨128,833424660,833425198⟩]
theorem checked15726 : checkPrefixCuts (2^48) 2065170433 9 Manual.Count131072.C015726.packed 128 cuts15726 = true := by
 decide +kernel
def pointBounds15726 : List (Nat × Nat × Nat) := [(2065209344,96888821339574,96889199781387),(2065274880,96889236619640,96889615061722)]
theorem point_links_checked15726 : (cuts15726.take 2).map (fun c => (2065170433-1+2*2^9*c.k,96888574782090+c.lower,96888953223747+c.upper)) = pointBounds15726 := by
 decide +kernel
def cuts15727 : List PrefixCut := [⟨38,246405569,246405727⟩,
⟨102,661795650,661796080⟩,
⟨128,830101194,830101735⟩]
theorem checked15727 : checkPrefixCuts (2^48) 2065301505 9 Manual.Count131072.C015727.packed 128 cuts15727 = true := by
 decide +kernel
def pointBounds15727 : List (Nat × Nat × Nat) := [(2065340416,96889654612319,96890033054672),(2065405952,96890070002400,96890448445025)]
theorem point_links_checked15727 : (cuts15727.take 2).map (fun c => (2065301505-1+2*2^9*c.k,96889408206750+c.lower,96889786648945+c.upper)) = pointBounds15727 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000178
