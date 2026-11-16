import PlattAssemblyKernel
import PlattCertificates.Count131072.C018736
import PlattCertificates.Count131072.C018737
import PlattCertificates.Count131072.C018738
import PlattCertificates.Count131072.C018739
import PlattCertificates.Count131072.C018740
import PlattCertificates.Count131072.C018741
import PlattCertificates.Count131072.C018742
import PlattCertificates.Count131072.C018743
import PlattCertificates.Count131072.C018744
import PlattCertificates.Count131072.C018745
import PlattCertificates.Count131072.C018746
import PlattCertificates.Count131072.C018747
import PlattCertificates.Count131072.C018748
import PlattCertificates.Count131072.C018749
import PlattCertificates.Count131072.C018750
import PlattCertificates.Count131072.C018751
import PlattCertificates.Count131072.C018752
import PlattCertificates.Count131072.C018753
import PlattCertificates.Count131072.C018754
import PlattCertificates.Count131072.C018755
import PlattCertificates.Count131072.C018756
import PlattCertificates.Count131072.C018757
import PlattCertificates.Count131072.C018758
import PlattCertificates.Count131072.C018759
import PlattCertificates.Count131072.C018760
import PlattCertificates.Count131072.C018761
import PlattCertificates.Count131072.C018762
import PlattCertificates.Count131072.C018763
import PlattCertificates.Count131072.C018764
import PlattCertificates.Count131072.C018765
import PlattCertificates.Count131072.C018766
import PlattCertificates.Count131072.C018767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000273
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18736 : List PrefixCut := [⟨46,248435524,248435670⟩,
⟨122,657868774,657869165⟩,
⟨128,688650125,688650535⟩]
theorem checked18736 : checkPrefixCuts (2^48) 2459697153 9 Manual.Count131072.C018736.packed 128 cuts18736 = true := by
 decide +kernel
def pointBounds18736 : List (Nat × Nat × Nat) := [(2459744256,99173756352928,99174136219236),(2459822080,99174165786178,99174545652731)]
theorem point_links_checked18736 : (cuts18736.take 2).map (fun c => (2459697153-1+2*2^9*c.k,99173507917404+c.lower,99173887783566+c.upper)) = pointBounds18736 := by
 decide +kernel
def cuts18737 : List PrefixCut := [⟨70,378982219,378982443⟩,
⟨128,687011489,687011899⟩]
theorem checked18737 : checkPrefixCuts (2^48) 2459828225 9 Manual.Count131072.C018737.packed 128 cuts18737 = true := by
 decide +kernel
def pointBounds18737 : List (Nat × Nat × Nat) := [(2459899904,99174575549748,99174955416544)]
theorem point_links_checked18737 : (cuts18737.take 1).map (fun c => (2459828225-1+2*2^9*c.k,99174196567529+c.lower,99174576434101+c.upper)) = pointBounds18737 := by
 decide +kernel
def cuts18738 : List PrefixCut := [⟨18,97487670,97487727⟩,
⟨94,505852300,505852609⟩,
⟨128,691551571,691551993⟩]
theorem checked18738 : checkPrefixCuts (2^48) 2459959297 9 Manual.Count131072.C018738.packed 128 cuts18738 = true := by
 decide +kernel
def pointBounds18738 : List (Nat × Nat × Nat) := [(2459977728,99174981066688,99175360933727),(2460055552,99175389431318,99175769298609)]
theorem point_links_checked18738 : (cuts18738.take 2).map (fun c => (2459959297-1+2*2^9*c.k,99174883579018+c.lower,99175263446000+c.upper)) = pointBounds18738 := by
 decide +kernel
def cuts18739 : List PrefixCut := [⟨42,228030054,228030191⟩,
⟨118,640030102,640030488⟩,
⟨128,694718381,694718800⟩]
theorem checked18739 : checkPrefixCuts (2^48) 2460090369 9 Manual.Count131072.C018739.packed 128 cuts18739 = true := by
 decide +kernel
def pointBounds18739 : List (Nat × Nat × Nat) := [(2460133376,99175803160643,99176183028184),(2460211200,99176215160691,99176595028481)]
theorem point_links_checked18739 : (cuts18739.take 2).map (fun c => (2460090369-1+2*2^9*c.k,99175575130589+c.lower,99175954997993+c.upper)) = pointBounds18739 := by
 decide +kernel
def cuts18740 : List PrefixCut := [⟨66,355468228,355468446⟩,
⟨128,690791550,690791969⟩]
theorem checked18740 : checkPrefixCuts (2^48) 2460221441 9 Manual.Count131072.C018740.packed 128 cuts18740 = true := by
 decide +kernel
def pointBounds18740 : List (Nat × Nat × Nat) := [(2460289024,99176625317198,99177005185239)]
theorem point_links_checked18740 : (cuts18740.take 1).map (fun c => (2460221441-1+2*2^9*c.k,99176269848970+c.lower,99176649716793+c.upper)) = pointBounds18740 := by
 decide +kernel
def cuts18741 : List PrefixCut := [⟨14,75964228,75964273⟩,
⟨90,489755571,489755869⟩,
⟨128,697275543,697275966⟩]
theorem checked18741 : checkPrefixCuts (2^48) 2460352513 9 Manual.Count131072.C018741.packed 128 cuts18741 = true := by
 decide +kernel
def pointBounds18741 : List (Nat × Nat × Nat) := [(2460366848,99177036604748,99177416473035),(2460444672,99177450396091,99177830264631)]
theorem point_links_checked18741 : (cuts18741.take 2).map (fun c => (2460352513-1+2*2^9*c.k,99176960640520+c.lower,99177340508762+c.upper)) = pointBounds18741 := by
 decide +kernel
def cuts18742 : List PrefixCut := [⟨38,206715915,206716037⟩,
⟨114,617506820,617507192⟩,
⟨128,693577792,693578209⟩]
theorem checked18742 : checkPrefixCuts (2^48) 2460483585 9 Manual.Count131072.C018742.packed 128 cuts18742 = true := by
 decide +kernel
def pointBounds18742 : List (Nat × Nat × Nat) := [(2460522496,99177864631978,99178244500765),(2460600320,99178275422883,99178655291920)]
theorem point_links_checked18742 : (cuts18742.take 2).map (fun c => (2460483585-1+2*2^9*c.k,99177657916063+c.lower,99178037784728+c.upper)) = pointBounds18742 := by
 decide +kernel
def cuts18743 : List PrefixCut := [⟨62,335622180,335622376⟩,
⟨128,692282676,692283090⟩]
theorem checked18743 : checkPrefixCuts (2^48) 2460614657 9 Manual.Count131072.C018743.packed 128 cuts18743 = true := by
 decide +kernel
def pointBounds18743 : List (Nat × Nat × Nat) := [(2460678144,99178687116035,99179066985313)]
theorem point_links_checked18743 : (cuts18743.take 1).map (fun c => (2460614657-1+2*2^9*c.k,99178351493855+c.lower,99178731362937+c.upper)) = pointBounds18743 := by
 decide +kernel
def cuts18744 : List PrefixCut := [⟨10,57764816,57764849⟩,
⟨86,461996974,461997251⟩,
⟨128,692817654,692818074⟩]
theorem checked18744 : checkPrefixCuts (2^48) 2460745729 9 Manual.Count131072.C018744.packed 128 cuts18744 = true := by
 decide +kernel
def pointBounds18744 : List (Nat × Nat × Nat) := [(2460755968,99179101541347,99179481410876),(2460833792,99179505773505,99179885643278)]
theorem point_links_checked18744 : (cuts18744.take 2).map (fun c => (2460745729-1+2*2^9*c.k,99179043776531+c.lower,99179423646027+c.upper)) = pointBounds18744 := by
 decide +kernel
def cuts18745 : List PrefixCut := [⟨34,183006576,183006686⟩,
⟨110,601967695,601968060⟩,
⟨128,702159554,702159982⟩]
theorem checked18745 : checkPrefixCuts (2^48) 2460876801 9 Manual.Count131072.C018745.packed 128 cuts18745 = true := by
 decide +kernel
def pointBounds18745 : List (Nat × Nat × Nat) := [(2460911616,99179919600761,99180299470787),(2460989440,99180338561880,99180718432161)]
theorem point_links_checked18745 : (cuts18745.take 2).map (fun c => (2460876801-1+2*2^9*c.k,99179736594185+c.lower,99180116464101+c.upper)) = pointBounds18745 := by
 decide +kernel
def cuts18746 : List PrefixCut := [⟨58,316926048,316926233⟩,
⟨128,696975589,696975997⟩]
theorem checked18746 : checkPrefixCuts (2^48) 2461007873 9 Manual.Count131072.C018746.packed 128 cuts18746 = true := by
 decide +kernel
def pointBounds18746 : List (Nat × Nat × Nat) := [(2461067264,99180755679787,99181135550316)]
theorem point_links_checked18746 : (cuts18746.take 1).map (fun c => (2461007873-1+2*2^9*c.k,99180438753739+c.lower,99180818624083+c.upper)) = pointBounds18746 := by
 decide +kernel
def cuts18747 : List PrefixCut := [⟨6,31908560,31908578⟩,
⟨82,441451975,441452241⟩,
⟨128,690305309,690305724⟩]
theorem checked18747 : checkPrefixCuts (2^48) 2461138945 9 Manual.Count131072.C018747.packed 128 cuts18747 = true := by
 decide +kernel
def pointBounds18747 : List (Nat × Nat × Nat) := [(2461145088,99181167637888,99181547508658),(2461222912,99181577181303,99181957052321)]
theorem point_links_checked18747 : (cuts18747.take 2).map (fun c => (2461138945-1+2*2^9*c.k,99181135729328+c.lower,99181515600080+c.upper)) = pointBounds18747 := by
 decide +kernel
def cuts18748 : List PrefixCut := [⟨30,161592002,161592102⟩,
⟨106,563218714,563219057⟩,
⟨128,681005466,681005879⟩]
theorem checked18748 : checkPrefixCuts (2^48) 2461270017 9 Manual.Count131072.C018748.packed 128 cuts18748 = true := by
 decide +kernel
def pointBounds18748 : List (Nat × Nat × Nat) := [(2461300736,99181987626639,99182367497906),(2461378560,99182389253351,99182769124861)]
theorem point_links_checked18748 : (cuts18748.take 2).map (fun c => (2461270017-1+2*2^9*c.k,99181826034637+c.lower,99182205905804+c.upper)) = pointBounds18748 := by
 decide +kernel
def cuts18749 : List PrefixCut := [⟨54,289201996,289202171⟩,
⟨128,696178016,696178433⟩]
theorem checked18749 : checkPrefixCuts (2^48) 2461401089 9 Manual.Count131072.C018749.packed 128 cuts18749 = true := by
 decide +kernel
def pointBounds18749 : List (Nat × Nat × Nat) := [(2461456384,99182796242099,99183176113854)]
theorem point_links_checked18749 : (cuts18749.take 1).map (fun c => (2461401089-1+2*2^9*c.k,99182507040103+c.lower,99182886911683+c.upper)) = pointBounds18749 := by
 decide +kernel
def cuts18750 : List PrefixCut := [⟨2,11434942,11434948⟩,
⟨78,420799244,420799489⟩,
⟨128,690995476,690995878⟩]
theorem checked18750 : checkPrefixCuts (2^48) 2461532161 9 Manual.Count131072.C018750.packed 128 cuts18750 = true := by
 decide +kernel
def pointBounds18750 : List (Nat × Nat × Nat) := [(2461534208,99183214653061,99183594525064),(2461612032,99183624017363,99184003889605)]
theorem point_links_checked18750 : (cuts18750.take 2).map (fun c => (2461532161-1+2*2^9*c.k,99183203218119+c.lower,99183583090116+c.upper)) = pointBounds18750 := by
 decide +kernel
def cuts18751 : List PrefixCut := [⟨26,144643593,144643678⟩,
⟨102,548951015,548951341⟩,
⟨128,689815314,689815726⟩]
theorem checked18751 : checkPrefixCuts (2^48) 2461663233 9 Manual.Count131072.C018751.packed 128 cuts18751 = true := by
 decide +kernel
def pointBounds18751 : List (Nat × Nat × Nat) := [(2461689856,99184038857188,99184418729672),(2461767680,99184443164610,99184823037335)]
theorem point_links_checked18751 : (cuts18751.take 2).map (fun c => (2461663233-1+2*2^9*c.k,99183894213595+c.lower,99184274085994+c.upper)) = pointBounds18751 := by
 decide +kernel
def cuts18752 : List PrefixCut := [⟨50,273263335,273263500⟩,
⟨126,685319838,685320250⟩,
⟨128,695380988,695381407⟩]
theorem checked18752 : checkPrefixCuts (2^48) 2461794305 9 Manual.Count131072.C018752.packed 128 cuts18752 = true := by
 decide +kernel
def pointBounds18752 : List (Nat × Nat × Nat) := [(2461845504,99184857292244,99185237165220),(2461923328,99185269348747,99185649221970)]
theorem point_links_checked18752 : (cuts18752.take 2).map (fun c => (2461794305-1+2*2^9*c.k,99184584028909+c.lower,99184963901720+c.upper)) = pointBounds18752 := by
 decide +kernel
def cuts18753 : List PrefixCut := [⟨74,395122575,395122814⟩,
⟨128,686769255,686769672⟩]
theorem checked18753 : checkPrefixCuts (2^48) 2461925377 9 Manual.Count131072.C018753.packed 128 cuts18753 = true := by
 decide +kernel
def pointBounds18753 : List (Nat × Nat × Nat) := [(2462001152,99185674532472,99186054405941)]
theorem point_links_checked18753 : (cuts18753.take 1).map (fun c => (2461925377-1+2*2^9*c.k,99185279409897+c.lower,99185659283127+c.upper)) = pointBounds18753 := by
 decide +kernel
def cuts18754 : List PrefixCut := [⟨22,118897590,118897660⟩,
⟨98,534573321,534573643⟩,
⟨128,699879664,699880089⟩]
theorem checked18754 : checkPrefixCuts (2^48) 2462056449 9 Manual.Count131072.C018754.packed 128 cuts18754 = true := by
 decide +kernel
def pointBounds18754 : List (Nat × Nat × Nat) := [(2462078976,99186085076742,99186464950459),(2462156800,99186500752473,99186880626442)]
theorem point_links_checked18754 : (cuts18754.take 2).map (fun c => (2462056449-1+2*2^9*c.k,99185966179152+c.lower,99186346052799+c.upper)) = pointBounds18754 := by
 decide +kernel
def cuts18755 : List PrefixCut := [⟨46,241782439,241782585⟩,
⟨122,656060147,656060545⟩,
⟨128,687953499,687953916⟩]
theorem checked18755 : checkPrefixCuts (2^48) 2462187521 9 Manual.Count131072.C018755.packed 128 cuts18755 = true := by
 decide +kernel
def pointBounds18755 : List (Nat × Nat × Nat) := [(2462234624,99186907841255,99187287715473),(2462312448,99187322118963,99187701993433)]
theorem point_links_checked18755 : (cuts18755.take 2).map (fun c => (2462187521-1+2*2^9*c.k,99186666058816+c.lower,99187045932888+c.upper)) = pointBounds18755 := by
 decide +kernel
def cuts18756 : List PrefixCut := [⟨70,373112069,373112295⟩,
⟨128,680944178,680944592⟩]
theorem checked18756 : checkPrefixCuts (2^48) 2462318593 9 Manual.Count131072.C018756.packed 128 cuts18756 = true := by
 decide +kernel
def pointBounds18756 : List (Nat × Nat × Nat) := [(2462390272,99187727124384,99188106999099)]
theorem point_links_checked18756 : (cuts18756.take 1).map (fun c => (2462318593-1+2*2^9*c.k,99187354012315+c.lower,99187733886804+c.upper)) = pointBounds18756 := by
 decide +kernel
def cuts18757 : List PrefixCut := [⟨18,101046891,101046953⟩,
⟨94,511398892,511399193⟩,
⟨128,691538190,691538605⟩]
theorem checked18757 : checkPrefixCuts (2^48) 2462449665 9 Manual.Count131072.C018757.packed 128 cuts18757 = true := by
 decide +kernel
def pointBounds18757 : List (Nat × Nat × Nat) := [(2462468096,99188136003384,99188515878349),(2462545920,99188546355385,99188926230589)]
theorem point_links_checked18757 : (cuts18757.take 2).map (fun c => (2462449665-1+2*2^9*c.k,99188034956493+c.lower,99188414831396+c.upper)) = pointBounds18757 := by
 decide +kernel
def cuts18758 : List PrefixCut := [⟨42,218083975,218084109⟩,
⟨118,627267223,627267598⟩,
⟨128,681557316,681557723⟩]
theorem checked18758 : checkPrefixCuts (2^48) 2462580737 9 Manual.Count131072.C018758.packed 128 cuts18758 = true := by
 decide +kernel
def pointBounds18758 : List (Nat × Nat × Nat) := [(2462623744,99188944578658,99189324454110),(2462701568,99189353761906,99189733637599)]
theorem point_links_checked18758 : (cuts18758.take 2).map (fun c => (2462580737-1+2*2^9*c.k,99188726494683+c.lower,99189106370001+c.upper)) = pointBounds18758 := by
 decide +kernel
def cuts18759 : List PrefixCut := [⟨66,364137854,364138073⟩,
⟨128,701407884,701408306⟩]
theorem checked18759 : checkPrefixCuts (2^48) 2462711809 9 Manual.Count131072.C018759.packed 128 cuts18759 = true := by
 decide +kernel
def pointBounds18759 : List (Nat × Nat × Nat) := [(2462779392,99189772189853,99190152065797)]
theorem point_links_checked18759 : (cuts18759.take 1).map (fun c => (2462711809-1+2*2^9*c.k,99189408051999+c.lower,99189787927724+c.upper)) = pointBounds18759 := by
 decide +kernel
def cuts18760 : List PrefixCut := [⟨14,71544463,71544508⟩,
⟨90,479774565,479774854⟩,
⟨128,687884712,687885123⟩]
theorem checked18760 : checkPrefixCuts (2^48) 2462842881 9 Manual.Count131072.C018760.packed 128 cuts18760 = true := by
 decide +kernel
def pointBounds18760 : List (Nat × Nat × Nat) := [(2462857216,99190181004346,99190560880538),(2462935040,99190589234448,99190969110884)]
theorem point_links_checked18760 : (cuts18760.take 2).map (fun c => (2462842881-1+2*2^9*c.k,99190109459883+c.lower,99190489336030+c.upper)) = pointBounds18760 := by
 decide +kernel
def cuts18761 : List PrefixCut := [⟨38,198392917,198393037⟩,
⟨114,608997077,608997438⟩,
⟨128,686933838,686934245⟩]
theorem checked18761 : checkPrefixCuts (2^48) 2462973953 9 Manual.Count131072.C018761.packed 128 cuts18761 = true := by
 decide +kernel
def pointBounds18761 : List (Nat × Nat × Nat) := [(2463012864,99190995737512,99191375614190),(2463090688,99191406341672,99191786218591)]
theorem point_links_checked18761 : (cuts18761.take 2).map (fun c => (2462973953-1+2*2^9*c.k,99190797344595+c.lower,99191177221153+c.upper)) = pointBounds18761 := by
 decide +kernel
def cuts18762 : List PrefixCut := [⟨62,338825273,338825476⟩,
⟨128,698096196,698096621⟩]
theorem checked18762 : checkPrefixCuts (2^48) 2463105025 9 Manual.Count131072.C018762.packed 128 cuts18762 = true := by
 decide +kernel
def pointBounds18762 : List (Nat × Nat × Nat) := [(2463168512,99191823103706,99192202980874)]
theorem point_links_checked18762 : (cuts18762.take 1).map (fun c => (2463105025-1+2*2^9*c.k,99191484278433+c.lower,99191864155398+c.upper)) = pointBounds18762 := by
 decide +kernel
def cuts18763 : List PrefixCut := [⟨10,54735392,54735422⟩,
⟨86,462329613,462329885⟩,
⟨128,694173900,694174311⟩]
theorem checked18763 : checkPrefixCuts (2^48) 2463236097 9 Manual.Count131072.C018763.packed 128 cuts18763 = true := by
 decide +kernel
def pointBounds18763 : List (Nat × Nat × Nat) := [(2463246336,99192237110021,99192616987441),(2463324160,99192644704242,99193024581904)]
theorem point_links_checked18763 : (cuts18763.take 2).map (fun c => (2463236097-1+2*2^9*c.k,99192182374629+c.lower,99192562252019+c.upper)) = pointBounds18763 := by
 decide +kernel
def cuts18764 : List PrefixCut := [⟨34,182478780,182478886⟩,
⟨110,592675351,592675704⟩,
⟨128,685910399,685910809⟩]
theorem checked18764 : checkPrefixCuts (2^48) 2463367169 9 Manual.Count131072.C018764.packed 128 cuts18764 = true := by
 decide +kernel
def pointBounds18764 : List (Nat × Nat × Nat) := [(2463401984,99193059027309,99193438905216),(2463479808,99193469223880,99193849102034)]
theorem point_links_checked18764 : (cuts18764.take 2).map (fun c => (2463367169-1+2*2^9*c.k,99192876548529+c.lower,99193256426330+c.upper)) = pointBounds18764 := by
 decide +kernel
def cuts18765 : List PrefixCut := [⟨58,316491407,316491600⟩,
⟨128,689644337,689644752⟩]
theorem checked18765 : checkPrefixCuts (2^48) 2463498241 9 Manual.Count131072.C018765.packed 128 cuts18765 = true := by
 decide +kernel
def pointBounds18765 : List (Nat × Nat × Nat) := [(2463557632,99193878950335,99194258828739)]
theorem point_links_checked18765 : (cuts18765.take 1).map (fun c => (2463498241-1+2*2^9*c.k,99193562458928+c.lower,99193942337139+c.upper)) = pointBounds18765 := by
 decide +kernel
def cuts18766 : List PrefixCut := [⟨6,32676068,32676088⟩,
⟨82,443290749,443291013⟩,
⟨128,689836074,689836487⟩]
theorem checked18766 : checkPrefixCuts (2^48) 2463629313 9 Manual.Count131072.C018766.packed 128 cuts18766 = true := by
 decide +kernel
def pointBounds18766 : List (Nat × Nat × Nat) := [(2463635456,99194284779333,99194664657979),(2463713280,99194695394014,99195075272904)]
theorem point_links_checked18766 : (cuts18766.take 2).map (fun c => (2463629313-1+2*2^9*c.k,99194252103265+c.lower,99194631981891+c.upper)) = pointBounds18766 := by
 decide +kernel
def cuts18767 : List PrefixCut := [⟨30,164170542,164170640⟩,
⟨106,578300777,578301126⟩,
⟨128,699395704,699396125⟩]
theorem checked18767 : checkPrefixCuts (2^48) 2463760385 9 Manual.Count131072.C018767.packed 128 cuts18767 = true := by
 decide +kernel
def pointBounds18767 : List (Nat × Nat × Nat) := [(2463791104,99195106109881,99195485989018),(2463868928,99195520240116,99195900119504)]
theorem point_links_checked18767 : (cuts18767.take 2).map (fun c => (2463760385-1+2*2^9*c.k,99194941939339+c.lower,99195321818378+c.upper)) = pointBounds18767 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000273
