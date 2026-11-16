import PlattAssemblyKernel
import PlattCertificates.Count131072.C013712
import PlattCertificates.Count131072.C013713
import PlattCertificates.Count131072.C013714
import PlattCertificates.Count131072.C013715
import PlattCertificates.Count131072.C013716
import PlattCertificates.Count131072.C013717
import PlattCertificates.Count131072.C013718
import PlattCertificates.Count131072.C013719
import PlattCertificates.Count131072.C013720
import PlattCertificates.Count131072.C013721
import PlattCertificates.Count131072.C013722
import PlattCertificates.Count131072.C013723
import PlattCertificates.Count131072.C013724
import PlattCertificates.Count131072.C013725
import PlattCertificates.Count131072.C013726
import PlattCertificates.Count131072.C013727
import PlattCertificates.Count131072.C013728
import PlattCertificates.Count131072.C013729
import PlattCertificates.Count131072.C013730
import PlattCertificates.Count131072.C013731
import PlattCertificates.Count131072.C013732
import PlattCertificates.Count131072.C013733
import PlattCertificates.Count131072.C013734
import PlattCertificates.Count131072.C013735
import PlattCertificates.Count131072.C013736
import PlattCertificates.Count131072.C013737
import PlattCertificates.Count131072.C013738
import PlattCertificates.Count131072.C013739
import PlattCertificates.Count131072.C013740
import PlattCertificates.Count131072.C013741
import PlattCertificates.Count131072.C013742
import PlattCertificates.Count131072.C013743
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13712 : List PrefixCut := [⟨14,102201142,102201215⟩,
⟨69,518342393,518342761⟩,
⟨124,926032385,926033039⟩,
⟨128,954159239,954159912⟩]
theorem checked13712 : checkPrefixCuts (2^48) 1801191425 9 Manual.Count131072.C013712.packed 128 cuts13712 = true := by
 decide +kernel
def pointBounds13712 : List (Nat × Nat × Nat) := [(1801205760,95088261952275,95088639179433),(1801262080,95088678093526,95089055320979),(1801318400,95089085783518,95089463011257)]
theorem point_links_checked13712 : (cuts13712.take 3).map (fun c => (1801191425-1+2*2^9*c.k,95088159751133+c.lower,95088536978218+c.upper)) = pointBounds13712 := by
 decide +kernel
def cuts13713 : List PrefixCut := [⟨51,381425454,381425718⟩,
⟨106,797683743,797684301⟩,
⟨128,970652199,970652875⟩]
theorem checked13713 : checkPrefixCuts (2^48) 1801322497 9 Manual.Count131072.C013713.packed 128 cuts13713 = true := by
 decide +kernel
def pointBounds13713 : List (Nat × Nat × Nat) := [(1801374720,95089495335826,95089872563848),(1801431040,95089911594115,95090288822431)]
theorem point_links_checked13713 : (cuts13713.take 2).map (fun c => (1801322497-1+2*2^9*c.k,95089113910372+c.lower,95089491138130+c.upper)) = pointBounds13713 := by
 decide +kernel
def cuts13714 : List PrefixCut := [⟨33,250776897,250777076⟩,
⟨88,667634278,667634751⟩,
⟨128,968238400,968239088⟩]
theorem checked13714 : checkPrefixCuts (2^48) 1801453569 9 Manual.Count131072.C013714.packed 128 cuts13714 = true := by
 decide +kernel
def pointBounds13714 : List (Nat × Nat × Nat) := [(1801487360,95090335339468,95090712568081),(1801543680,95090752196849,95091129425756)]
theorem point_links_checked13714 : (cuts13714.take 2).map (fun c => (1801453569-1+2*2^9*c.k,95090084562571+c.lower,95090461791005+c.upper)) = pointBounds13714 := by
 decide +kernel
def cuts13715 : List PrefixCut := [⟨15,109209481,109209561⟩,
⟨70,521509996,521510363⟩,
⟨125,926923534,926924185⟩,
⟨128,950982361,950983030⟩]
theorem checked13715 : checkPrefixCuts (2^48) 1801584641 9 Manual.Count131072.C013715.packed 128 cuts13715 = true := by
 decide +kernel
def pointBounds13715 : List (Nat × Nat × Nat) := [(1801600000,95091162010452,95091539239654),(1801656320,95091574310967,95091951540456),(1801712640,95091979724505,95092356954278)]
theorem point_links_checked13715 : (cuts13715.take 3).map (fun c => (1801584641-1+2*2^9*c.k,95091052800971+c.lower,95091430030093+c.upper)) = pointBounds13715 := by
 decide +kernel
def cuts13716 : List PrefixCut := [⟨52,388059716,388059990⟩,
⟨107,802196099,802196659⟩,
⟨128,961535999,961536671⟩]
theorem checked13716 : checkPrefixCuts (2^48) 1801715713 9 Manual.Count131072.C013716.packed 128 cuts13716 = true := by
 decide +kernel
def pointBounds13716 : List (Nat × Nat × Nat) := [(1801768960,95092391843048,95092769073113),(1801825280,95092805979431,95093183209782)]
theorem point_links_checked13716 : (cuts13716.take 2).map (fun c => (1801715713-1+2*2^9*c.k,95092003783332+c.lower,95092381013123+c.upper)) = pointBounds13716 := by
 decide +kernel
def cuts13717 : List PrefixCut := [⟨34,258376549,258376727⟩,
⟨89,666707381,666707846⟩,
⟨128,957248684,957249352⟩]
theorem checked13717 : checkPrefixCuts (2^48) 1801846785 9 Manual.Count131072.C013717.packed 128 cuts13717 = true := by
 decide +kernel
def pointBounds13717 : List (Nat × Nat × Nat) := [(1801881600,95093223695880,95093600926521),(1801937920,95093632026712,95094009257640)]
theorem point_links_checked13717 : (cuts13717.take 2).map (fun c => (1801846785-1+2*2^9*c.k,95092965319331+c.lower,95093342549794+c.upper)) = pointBounds13717 := by
 decide +kernel
def cuts13718 : List PrefixCut := [⟨16,122619029,122619114⟩,
⟨71,539983923,539984306⟩,
⟨126,957179613,957180289⟩,
⟨128,971080703,971081389⟩]
theorem checked13718 : checkPrefixCuts (2^48) 1801977857 9 Manual.Count131072.C013718.packed 128 cuts13718 = true := by
 decide +kernel
def pointBounds13718 : List (Nat × Nat × Nat) := [(1801994240,95094045187044,95094422418260),(1802050560,95094462551938,95094839783452),(1802106880,95094879747628,95095256979435)]
theorem point_links_checked13718 : (cuts13718.take 3).map (fun c => (1801977857-1+2*2^9*c.k,95093922568015+c.lower,95094299799146+c.upper)) = pointBounds13718 := by
 decide +kernel
def cuts13719 : List PrefixCut := [⟨53,394378681,394378950⟩,
⟨108,800771494,800772052⟩,
⟨128,948050629,948051292⟩]
theorem checked13719 : checkPrefixCuts (2^48) 1802108929 9 Manual.Count131072.C013719.packed 128 cuts13719 = true := by
 decide +kernel
def pointBounds13719 : List (Nat × Nat × Nat) := [(1802163200,95095288027399,95095665259485),(1802219520,95095694420212,95096071652587)]
theorem point_links_checked13719 : (cuts13719.take 2).map (fun c => (1802108929-1+2*2^9*c.k,95094893648718+c.lower,95095270880535+c.upper)) = pointBounds13719 := by
 decide +kernel
def cuts13720 : List PrefixCut := [⟨35,256446014,256446194⟩,
⟨91,669997329,669997800⟩,
⟨128,951729528,951730198⟩]
theorem checked13720 : checkPrefixCuts (2^48) 1802240001 9 Manual.Count131072.C013720.packed 128 cuts13720 = true := by
 decide +kernel
def pointBounds13720 : List (Nat × Nat × Nat) := [(1802275840,95096098145361,95096475378021),(1802333184,95096511696676,95096888929627)]
theorem point_links_checked13720 : (cuts13720.take 2).map (fun c => (1802240001-1+2*2^9*c.k,95095841699347+c.lower,95096218931827+c.upper)) = pointBounds13720 := by
 decide +kernel
def cuts13721 : List PrefixCut := [⟨19,142113229,142113326⟩,
⟨75,569536925,569537319⟩,
⟨128,973054945,973055621⟩]
theorem checked13721 : checkPrefixCuts (2^48) 1802371073 9 Manual.Count131072.C013721.packed 128 cuts13721 = true := by
 decide +kernel
def pointBounds13721 : List (Nat × Nat × Nat) := [(1802390528,95096935542104,95097312775351),(1802447872,95097362965800,95097740199344)]
theorem point_links_checked13721 : (cuts13721.take 2).map (fun c => (1802371073-1+2*2^9*c.k,95096793428875+c.lower,95097170662025+c.upper)) = pointBounds13721 := by
 decide +kernel
def cuts13722 : List PrefixCut := [⟨3,22955187,22955203⟩,
⟨59,446603983,446604295⟩,
⟨115,870551610,870552215⟩,
⟨128,967362809,967363483⟩]
theorem checked13722 : checkPrefixCuts (2^48) 1802502145 9 Manual.Count131072.C013722.packed 128 cuts13722 = true := by
 decide +kernel
def pointBounds13722 : List (Nat × Nat × Nat) := [(1802505216,95097789439007,95098166672849),(1802562560,95098213087803,95098590321941),(1802619904,95098637035430,95099014269861)]
theorem point_links_checked13722 : (cuts13722.take 3).map (fun c => (1802502145-1+2*2^9*c.k,95097766483820+c.lower,95098143717646+c.upper)) = pointBounds13722 := by
 decide +kernel
def cuts13723 : List PrefixCut := [⟨43,317441987,317442210⟩,
⟨99,733711719,733712235⟩,
⟨128,949804514,949805180⟩]
theorem checked13723 : checkPrefixCuts (2^48) 1802633217 9 Manual.Count131072.C013723.packed 128 cuts13723 = true := by
 decide +kernel
def pointBounds13723 : List (Nat × Nat × Nat) := [(1802677248,95099051288616,95099428523339),(1802734592,95099467558348,95099844793364)]
theorem point_links_checked13723 : (cuts13723.take 2).map (fun c => (1802633217-1+2*2^9*c.k,95098733846629+c.lower,95099111081129+c.upper)) = pointBounds13723 := by
 decide +kernel
def cuts13724 : List PrefixCut := [⟨27,202661879,202662022⟩,
⟨83,622652336,622652774⟩,
⟨128,961289153,961289833⟩]
theorem checked13724 : checkPrefixCuts (2^48) 1802764289 9 Manual.Count131072.C013724.packed 128 cuts13724 = true := by
 decide +kernel
def pointBounds13724 : List (Nat × Nat × Nat) := [(1802791936,95099886313022,95100263548331),(1802849280,95100306303479,95100683539083)]
theorem point_links_checked13724 : (cuts13724.take 2).map (fun c => (1802764289-1+2*2^9*c.k,95099683651143+c.lower,95100060886309+c.upper)) = pointBounds13724 := by
 decide +kernel
def cuts13725 : List PrefixCut := [⟨11,82276994,82277051⟩,
⟨67,504738583,504738937⟩,
⟨123,921878859,921879504⟩,
⟨128,960438691,960439363⟩]
theorem checked13725 : checkPrefixCuts (2^48) 1802895361 9 Manual.Count131072.C013725.packed 128 cuts13725 = true := by
 decide +kernel
def pointBounds13725 : List (Nat × Nat × Nat) := [(1802906624,95100727217290,95101104453193),(1802963968,95101149678879,95101526915079),(1803021312,95101566819155,95101944055646)]
theorem point_links_checked13725 : (cuts13725.take 3).map (fun c => (1802895361-1+2*2^9*c.k,95100644940296+c.lower,95101022176142+c.upper)) = pointBounds13725 := by
 decide +kernel
def cuts13726 : List PrefixCut := [⟨51,372322786,372323050⟩,
⟨107,788187737,788188291⟩,
⟨128,948816736,948817401⟩]
theorem checked13726 : checkPrefixCuts (2^48) 1803026433 9 Manual.Count131072.C013726.packed 128 cuts13726 = true := by
 decide +kernel
def pointBounds13726 : List (Nat × Nat × Nat) := [(1803078656,95101977701773,95102354938555),(1803136000,95102393566724,95102770803796)]
theorem point_links_checked13726 : (cuts13726.take 2).map (fun c => (1803026433-1+2*2^9*c.k,95101605378987+c.lower,95101982615505+c.upper)) = pointBounds13726 := by
 decide +kernel
def cuts13727 : List PrefixCut := [⟨35,266930283,266930470⟩,
⟨91,691510055,691510538⟩,
⟨128,974191517,974192200⟩]
theorem checked13727 : checkPrefixCuts (2^48) 1803157505 9 Manual.Count131072.C013727.packed 128 cuts13727 = true := by
 decide +kernel
def pointBounds13727 : List (Nat × Nat × Nat) := [(1803193344,95102821126006,95103198363376),(1803250688,95103245705778,95103622943444)]
theorem point_links_checked13727 : (cuts13727.take 2).map (fun c => (1803157505-1+2*2^9*c.k,95102554195723+c.lower,95102931432906+c.upper)) = pointBounds13727 := by
 decide +kernel
def cuts13728 : List PrefixCut := [⟨19,137982597,137982695⟩,
⟨75,556604095,556604489⟩,
⟨128,949459385,949460060⟩]
theorem checked13728 : checkPrefixCuts (2^48) 1803288577 9 Manual.Count131072.C013728.packed 128 cuts13728 = true := by
 decide +kernel
def pointBounds13728 : List (Nat × Nat × Nat) := [(1803308032,95103666369837,95104043607801),(1803365376,95104084991335,95104462229595)]
theorem point_links_checked13728 : (cuts13728.take 2).map (fun c => (1803288577-1+2*2^9*c.k,95103528387240+c.lower,95103905625106+c.upper)) = pointBounds13728 := by
 decide +kernel
def cuts13729 : List PrefixCut := [⟨3,25752914,25752933⟩,
⟨59,441070197,441070504⟩,
⟨115,861212467,861213061⟩,
⟨128,960627559,960628221⟩]
theorem checked13729 : checkPrefixCuts (2^48) 1803419649 9 Manual.Count131072.C013729.packed 128 cuts13729 = true := by
 decide +kernel
def pointBounds13729 : List (Nat × Nat × Nat) := [(1803422720,95104503599539,95104880838099),(1803480064,95104918916822,95105296155670),(1803537408,95105339059092,95105716298227)]
theorem point_links_checked13729 : (cuts13729.take 3).map (fun c => (1803419649-1+2*2^9*c.k,95104477846625+c.lower,95104855085166+c.upper)) = pointBounds13729 := by
 decide +kernel
def cuts13730 : List PrefixCut := [⟨43,318060821,318061043⟩,
⟨99,743950647,743951159⟩,
⟨128,958216930,958217594⟩]
theorem checked13730 : checkPrefixCuts (2^48) 1803550721 9 Manual.Count131072.C013730.packed 128 cuts13730 = true := by
 decide +kernel
def pointBounds13730 : List (Nat × Nat × Nat) := [(1803594752,95105756535005,95106133774430),(1803652096,95106182424831,95106559664546)]
theorem point_links_checked13730 : (cuts13730.take 2).map (fun c => (1803550721-1+2*2^9*c.k,95105438474184+c.lower,95105815713387+c.upper)) = pointBounds13730 := by
 decide +kernel
def cuts13731 : List PrefixCut := [⟨27,202870903,202871045⟩,
⟨83,620306910,620307342⟩,
⟨128,955494522,955495188⟩]
theorem checked13731 : checkPrefixCuts (2^48) 1803681793 9 Manual.Count131072.C013731.packed 128 cuts13731 = true := by
 decide +kernel
def pointBounds13731 : List (Nat × Nat × Nat) := [(1803709440,95106599562017,95106976802026),(1803766784,95107016998024,95107394238323)]
theorem point_links_checked13731 : (cuts13731.take 2).map (fun c => (1803681793-1+2*2^9*c.k,95106396691114+c.lower,95106773930981+c.upper)) = pointBounds13731 := by
 decide +kernel
def cuts13732 : List PrefixCut := [⟨11,82547234,82547292⟩,
⟨67,504481879,504482233⟩,
⟨123,921722129,921722783⟩,
⟨128,961822678,961823360⟩]
theorem checked13732 : checkPrefixCuts (2^48) 1803812865 9 Manual.Count131072.C013732.packed 128 cuts13732 = true := by
 decide +kernel
def pointBounds13732 : List (Nat × Nat × Nat) := [(1803824128,95107434732870,95107811973461),(1803881472,95107856667515,95108233908402),(1803938816,95108273907765,95108651148952)]
theorem point_links_checked13732 : (cuts13732.take 3).map (fun c => (1803812865-1+2*2^9*c.k,95107352185636+c.lower,95107729426169+c.upper)) = pointBounds13732 := by
 decide +kernel
def cuts13733 : List PrefixCut := [⟨51,385552078,385552343⟩,
⟨107,809474907,809475468⟩,
⟨128,963469256,963469923⟩]
theorem checked13733 : checkPrefixCuts (2^48) 1803943937 9 Manual.Count131072.C013733.packed 128 cuts13733 = true := by
 decide +kernel
def pointBounds13733 : List (Nat × Nat × Nat) := [(1803996160,95108699560392,95109076801872),(1804053504,95109123483221,95109500724997)]
theorem point_links_checked13733 : (cuts13733.take 2).map (fun c => (1803943937-1+2*2^9*c.k,95108314008314+c.lower,95108691249529+c.upper)) = pointBounds13733 := by
 decide +kernel
def cuts13734 : List PrefixCut := [⟨35,266794456,266794642⟩,
⟨91,689754126,689754608⟩,
⟨128,966675466,966676139⟩]
theorem checked13734 : checkPrefixCuts (2^48) 1804075009 9 Manual.Count131072.C013734.packed 128 cuts13734 = true := by
 decide +kernel
def pointBounds13734 : List (Nat × Nat × Nat) := [(1804110848,95109544272026,95109921514094),(1804168192,95109967231696,95110344474060)]
theorem point_links_checked13734 : (cuts13734.take 2).map (fun c => (1804075009-1+2*2^9*c.k,95109277477570+c.lower,95109654719452+c.upper)) = pointBounds13734 := by
 decide +kernel
def cuts13735 : List PrefixCut := [⟨19,139940542,139940639⟩,
⟨75,559597323,559597715⟩,
⟨128,961300891,961301564⟩]
theorem checked13735 : checkPrefixCuts (2^48) 1804206081 9 Manual.Count131072.C013735.packed 128 cuts13735 = true := by
 decide +kernel
def pointBounds13735 : List (Nat × Nat × Nat) := [(1804225536,95110384093578,95110761336230),(1804282880,95110803750359,95111180993306)]
theorem point_links_checked13735 : (cuts13735.take 2).map (fun c => (1804206081-1+2*2^9*c.k,95110244153036+c.lower,95110621395591+c.upper)) = pointBounds13735 := by
 decide +kernel
def cuts13736 : List PrefixCut := [⟨3,21215851,21215867⟩,
⟨59,434450125,434450438⟩,
⟨115,847359267,847359868⟩,
⟨128,945787867,945788538⟩]
theorem checked13736 : checkPrefixCuts (2^48) 1804337153 9 Manual.Count131072.C013736.packed 128 cuts13736 = true := by
 decide +kernel
def pointBounds13736 : List (Nat × Nat × Nat) := [(1804340224,95111226669778,95111603913022),(1804397568,95111639904052,95112017147593),(1804454912,95112052813194,95112430057023)]
theorem point_links_checked13736 : (cuts13736.take 3).map (fun c => (1804337153-1+2*2^9*c.k,95111205453927+c.lower,95111582697155+c.upper)) = pointBounds13736 := by
 decide +kernel
def cuts13737 : List PrefixCut := [⟨43,329130058,329130288⟩,
⟨99,743572688,743573214⟩,
⟨128,964281059,964281743⟩]
theorem checked13737 : checkPrefixCuts (2^48) 1804468225 9 Manual.Count131072.C013737.packed 128 cuts13737 = true := by
 decide +kernel
def pointBounds13737 : List (Nat × Nat × Nat) := [(1804512256,95112480371852,95112857615981),(1804569600,95112894814482,95113272058907)]
theorem point_links_checked13737 : (cuts13737.take 2).map (fun c => (1804468225-1+2*2^9*c.k,95112151241794+c.lower,95112528485693+c.upper)) = pointBounds13737 := by
 decide +kernel
def cuts13738 : List PrefixCut := [⟨27,210566521,210566668⟩,
⟨83,621707392,621707821⟩,
⟨128,963899119,963899786⟩]
theorem checked13738 : checkPrefixCuts (2^48) 1804599297 9 Manual.Count131072.C013738.packed 128 cuts13738 = true := by
 decide +kernel
def pointBounds13738 : List (Nat × Nat × Nat) := [(1804626944,95113326089374,95113703334104),(1804684288,95113737230245,95114114475257)]
theorem point_links_checked13738 : (cuts13738.take 2).map (fun c => (1804599297-1+2*2^9*c.k,95113115522853+c.lower,95113492767436+c.upper)) = pointBounds13738 := by
 decide +kernel
def cuts13739 : List PrefixCut := [⟨11,78762105,78762161⟩,
⟨67,490188852,490189195⟩,
⟨123,913611217,913611853⟩,
⟨128,952443752,952444416⟩]
theorem checked13739 : checkPrefixCuts (2^48) 1804730369 9 Manual.Count131072.C013739.packed 128 cuts13739 = true := by
 decide +kernel
def pointBounds13739 : List (Nat × Nat × Nat) := [(1804741632,95114158184077,95114535429383),(1804798976,95114569610824,95114946856417),(1804856320,95114993033189,95115370279075)]
theorem point_links_checked13739 : (cuts13739.take 3).map (fun c => (1804730369-1+2*2^9*c.k,95114079421972+c.lower,95114456667222+c.upper)) = pointBounds13739 := by
 decide +kernel
def cuts13740 : List PrefixCut := [⟨51,382704907,382705173⟩,
⟨107,805788500,805789059⟩,
⟨128,960484273,960484942⟩]
theorem checked13740 : checkPrefixCuts (2^48) 1804861441 9 Manual.Count131072.C013740.packed 128 cuts13740 = true := by
 decide +kernel
def pointBounds13740 : List (Nat × Nat × Nat) := [(1804913664,95115414570631,95115791816811),(1804971008,95115837654224,95116214900697)]
theorem point_links_checked13740 : (cuts13740.take 2).map (fun c => (1804861441-1+2*2^9*c.k,95115031865724+c.lower,95115409111638+c.upper)) = pointBounds13740 := by
 decide +kernel
def cuts13741 : List PrefixCut := [⟨35,254651428,254651607⟩,
⟨91,671470531,671471004⟩,
⟨128,951681629,951682295⟩]
theorem checked13741 : checkPrefixCuts (2^48) 1804992513 9 Manual.Count131072.C013741.packed 128 cuts13741 = true := by
 decide +kernel
def pointBounds13741 : List (Nat × Nat × Nat) := [(1805028352,95116247001425,95116624248187),(1805085696,95116663820528,95117041067584)]
theorem point_links_checked13741 : (cuts13741.take 2).map (fun c => (1804992513-1+2*2^9*c.k,95115992349997+c.lower,95116369596580+c.upper)) = pointBounds13741 := by
 decide +kernel
def cuts13742 : List PrefixCut := [⟨19,141584648,141584745⟩,
⟨75,552140265,552140652⟩,
⟨128,942881135,942881798⟩]
theorem checked13742 : checkPrefixCuts (2^48) 1805123585 9 Manual.Count131072.C013742.packed 128 cuts13742 = true := by
 decide +kernel
def pointBounds13742 : List (Nat × Nat × Nat) := [(1805143040,95117085616274,95117462863620),(1805200384,95117496171891,95117873419527)]
theorem point_links_checked13742 : (cuts13742.take 2).map (fun c => (1805123585-1+2*2^9*c.k,95116944031626+c.lower,95117321278875+c.upper)) = pointBounds13742 := by
 decide +kernel
def cuts13743 : List PrefixCut := [⟨3,21984667,21984682⟩,
⟨59,439998202,439998509⟩,
⟨115,856595231,856595827⟩,
⟨128,955441543,955442205⟩]
theorem checked13743 : checkPrefixCuts (2^48) 1805254657 9 Manual.Count131072.C013743.packed 128 cuts13743 = true := by
 decide +kernel
def pointBounds13743 : List (Nat × Nat × Nat) := [(1805257728,95117908897428,95118286145355),(1805315072,95118326910963,95118704159182),(1805372416,95118743507992,95119120756500)]
theorem point_links_checked13743 : (cuts13743.take 3).map (fun c => (1805254657-1+2*2^9*c.k,95117886912761+c.lower,95118264160673+c.upper)) = pointBounds13743 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000116
