import PlattAssemblyKernel
import PlattCertificates.Count131072.C026720
import PlattCertificates.Count131072.C026721
import PlattCertificates.Count131072.C026722
import PlattCertificates.Count131072.C026723
import PlattCertificates.Count131072.C026724
import PlattCertificates.Count131072.C026725
import PlattCertificates.Count131072.C026726
import PlattCertificates.Count131072.C026727
import PlattCertificates.Count131072.C026728
import PlattCertificates.Count131072.C026729
import PlattCertificates.Count131072.C026730
import PlattCertificates.Count131072.C026731
import PlattCertificates.Count131072.C026732
import PlattCertificates.Count131072.C026733
import PlattCertificates.Count131072.C026734
import PlattCertificates.Count131072.C026735
import PlattCertificates.Count131072.C026736
import PlattCertificates.Count131072.C026737
import PlattCertificates.Count131072.C026738
import PlattCertificates.Count131072.C026739
import PlattCertificates.Count131072.C026740
import PlattCertificates.Count131072.C026741
import PlattCertificates.Count131072.C026742
import PlattCertificates.Count131072.C026743
import PlattCertificates.Count131072.C026744
import PlattCertificates.Count131072.C026745
import PlattCertificates.Count131072.C026746
import PlattCertificates.Count131072.C026747
import PlattCertificates.Count131072.C026748
import PlattCertificates.Count131072.C026749
import PlattCertificates.Count131072.C026750
import PlattCertificates.Count131072.C026751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000210
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26720 : List PrefixCut := [⟨100,370726384,370726589⟩,
⟨128,475728780,475729044⟩]
theorem checked26720 : checkPrefixCuts (2^48) 3506176001 9 Manual.Count131072.C026720.packed 128 cuts26720 = true := by
 decide +kernel
def pointBounds26720 : List (Nat × Nat × Nat) := [(3506278400,103750876210381,103751258704437)]
theorem point_links_checked26720 : (cuts26720.take 1).map (fun c => (3506176001-1+2*2^9*c.k,103750505483997+c.lower,103750887977848+c.upper)) = pointBounds26720 := by
 decide +kernel
def cuts26721 : List PrefixCut := [⟨80,299107586,299107754⟩,
⟨128,480447228,480447495⟩]
theorem checked26721 : checkPrefixCuts (2^48) 3506307073 9 Manual.Count131072.C026721.packed 128 cuts26721 = true := by
 decide +kernel
def pointBounds26721 : List (Nat × Nat × Nat) := [(3506388992,103751280320363,103751662814646)]
theorem point_links_checked26721 : (cuts26721.take 1).map (fun c => (3506307073-1+2*2^9*c.k,103750981212777+c.lower,103751363706892+c.upper)) = pointBounds26721 := by
 decide +kernel
def cuts26722 : List PrefixCut := [⟨60,221232479,221232605⟩,
⟨128,474649717,474649986⟩]
theorem checked26722 : checkPrefixCuts (2^48) 3506438145 9 Manual.Count131072.C026722.packed 128 cuts26722 = true := by
 decide +kernel
def pointBounds26722 : List (Nat × Nat × Nat) := [(3506499584,103751682892484,103752065386992)]
theorem point_links_checked26722 : (cuts26722.take 1).map (fun c => (3506438145-1+2*2^9*c.k,103751461660005+c.lower,103751844154387+c.upper)) = pointBounds26722 := by
 decide +kernel
def cuts26723 : List PrefixCut := [⟨40,154520259,154520344⟩,
⟨128,482980058,482980330⟩]
theorem checked26723 : checkPrefixCuts (2^48) 3506569217 9 Manual.Count131072.C026723.packed 128 cuts26723 = true := by
 decide +kernel
def pointBounds26723 : List (Nat × Nat × Nat) := [(3506610176,103752090829981,103752473324717)]
theorem point_links_checked26723 : (cuts26723.take 1).map (fun c => (3506569217-1+2*2^9*c.k,103751936309722+c.lower,103752318804373+c.upper)) = pointBounds26723 := by
 decide +kernel
def cuts26724 : List PrefixCut := [⟨20,75130390,75130430⟩,
⟨128,480473723,480473986⟩]
theorem checked26724 : checkPrefixCuts (2^48) 3506700289 9 Manual.Count131072.C026724.packed 128 cuts26724 = true := by
 decide +kernel
def pointBounds26724 : List (Nat × Nat × Nat) := [(3506720768,103752494420170,103752876915133),(3506831360,103752899763503,103753282258689)]
theorem point_links_checked26724 : (cuts26724.take 2).map (fun c => (3506700289-1+2*2^9*c.k,103752419289780+c.lower,103752801784703+c.upper)) = pointBounds26724 := by
 decide +kernel
def cuts26725 : List PrefixCut := [⟨108,401156798,401157022⟩,
⟨128,477004364,477004629⟩]
theorem checked26725 : checkPrefixCuts (2^48) 3506831361 9 Manual.Count131072.C026725.packed 128 cuts26725 = true := by
 decide +kernel
def pointBounds26725 : List (Nat × Nat × Nat) := [(3506941952,103753300920301,103753683415711)]
theorem point_links_checked26725 : (cuts26725.take 1).map (fun c => (3506831361-1+2*2^9*c.k,103752899763503+c.lower,103753282258689+c.upper)) = pointBounds26725 := by
 decide +kernel
def cuts26726 : List PrefixCut := [⟨88,327062397,327062580⟩,
⟨128,477628663,477628931⟩]
theorem checked26726 : checkPrefixCuts (2^48) 3506962433 9 Manual.Count131072.C026726.packed 128 cuts26726 = true := by
 decide +kernel
def pointBounds26726 : List (Nat × Nat × Nat) := [(3507052544,103753703830264,103754086325898)]
theorem point_links_checked26726 : (cuts26726.take 1).map (fun c => (3506962433-1+2*2^9*c.k,103753376767867+c.lower,103753759263318+c.upper)) = pointBounds26726 := by
 decide +kernel
def cuts26727 : List PrefixCut := [⟨68,256022863,256023007⟩,
⟨128,478493717,478493984⟩]
theorem checked26727 : checkPrefixCuts (2^48) 3507093505 9 Manual.Count131072.C026727.packed 128 cuts26727 = true := by
 decide +kernel
def pointBounds26727 : List (Nat × Nat × Nat) := [(3507163136,103754110419393,103754492915256)]
theorem point_links_checked26727 : (cuts26727.take 1).map (fun c => (3507093505-1+2*2^9*c.k,103753854396530+c.lower,103754236892249+c.upper)) = pointBounds26727 := by
 decide +kernel
def cuts26728 : List PrefixCut := [⟨48,178648014,178648113⟩,
⟨128,477111443,477111715⟩]
theorem checked26728 : checkPrefixCuts (2^48) 3507224577 9 Manual.Count131072.C026728.packed 128 cuts26728 = true := by
 decide +kernel
def pointBounds26728 : List (Nat × Nat × Nat) := [(3507273728,103754511538261,103754894034346)]
theorem point_links_checked26728 : (cuts26728.take 1).map (fun c => (3507224577-1+2*2^9*c.k,103754332890247+c.lower,103754715386233+c.upper)) = pointBounds26728 := by
 decide +kernel
def cuts26729 : List PrefixCut := [⟨28,106414692,106414752⟩,
⟨128,481427151,481427421⟩]
theorem checked26729 : checkPrefixCuts (2^48) 3507355649 9 Manual.Count131072.C026729.packed 128 cuts26729 = true := by
 decide +kernel
def pointBounds26729 : List (Nat × Nat × Nat) := [(3507384320,103754916416382,103755298912700)]
theorem point_links_checked26729 : (cuts26729.take 1).map (fun c => (3507355649-1+2*2^9*c.k,103754810001690+c.lower,103755192497948+c.upper)) = pointBounds26729 := by
 decide +kernel
def cuts26730 : List PrefixCut := [⟨8,30254116,30254131⟩,
⟨116,441285842,441286085⟩,
⟨128,488069774,488070043⟩]
theorem checked26730 : checkPrefixCuts (2^48) 3507486721 9 Manual.Count131072.C026730.packed 128 cuts26730 = true := by
 decide +kernel
def pointBounds26730 : List (Nat × Nat × Nat) := [(3507494912,103755321682957,103755704179500),(3507605504,103755732714683,103756115211454)]
theorem point_links_checked26730 : (cuts26730.take 2).map (fun c => (3507486721-1+2*2^9*c.k,103755291428841+c.lower,103755673925369+c.upper)) = pointBounds26730 := by
 decide +kernel
def cuts26731 : List PrefixCut := [⟨96,355728867,355729061⟩,
⟨128,471521128,471521388⟩]
theorem checked26731 : checkPrefixCuts (2^48) 3507617793 9 Manual.Count131072.C026731.packed 128 cuts26731 = true := by
 decide +kernel
def pointBounds26731 : List (Nat × Nat × Nat) := [(3507716096,103756135227482,103756517724473)]
theorem point_links_checked26731 : (cuts26731.take 1).map (fun c => (3507617793-1+2*2^9*c.k,103755779498615+c.lower,103756161995412+c.upper)) = pointBounds26731 := by
 decide +kernel
def cuts26732 : List PrefixCut := [⟨76,290479154,290479313⟩,
⟨128,487311191,487311458⟩]
theorem checked26732 : checkPrefixCuts (2^48) 3507748865 9 Manual.Count131072.C026732.packed 128 cuts26732 = true := by
 decide +kernel
def pointBounds26732 : List (Nat × Nat × Nat) := [(3507826688,103756541498897,103756923996113)]
theorem point_links_checked26732 : (cuts26732.take 1).map (fun c => (3507748865-1+2*2^9*c.k,103756251019743+c.lower,103756633516800+c.upper)) = pointBounds26732 := by
 decide +kernel
def cuts26733 : List PrefixCut := [⟨56,212235036,212235155⟩,
⟨128,480633095,480633366⟩]
theorem checked26733 : checkPrefixCuts (2^48) 3507879937 9 Manual.Count131072.C026733.packed 128 cuts26733 = true := by
 decide +kernel
def pointBounds26733 : List (Nat × Nat × Nat) := [(3507937280,103756950565970,103757333063413)]
theorem point_links_checked26733 : (cuts26733.take 1).map (fun c => (3507879937-1+2*2^9*c.k,103756738330934+c.lower,103757120828258+c.upper)) = pointBounds26733 := by
 decide +kernel
def cuts26734 : List PrefixCut := [⟨36,131268265,131268341⟩,
⟨128,474918290,474918559⟩]
theorem checked26734 : checkPrefixCuts (2^48) 3508011009 9 Manual.Count131072.C026734.packed 128 cuts26734 = true := by
 decide +kernel
def pointBounds26734 : List (Nat × Nat × Nat) := [(3508047872,103757350232294,103757732729965)]
theorem point_links_checked26734 : (cuts26734.take 1).map (fun c => (3508011009-1+2*2^9*c.k,103757218964029+c.lower,103757601461624+c.upper)) = pointBounds26734 := by
 decide +kernel
def cuts26735 : List PrefixCut := [⟨16,55281610,55281643⟩,
⟨124,456687913,456688174⟩,
⟨128,472252881,472253152⟩]
theorem checked26735 : checkPrefixCuts (2^48) 3508142081 9 Manual.Count131072.C026735.packed 128 cuts26735 = true := by
 decide +kernel
def pointBounds26735 : List (Nat × Nat × Nat) := [(3508158464,103757749163929,103758131661826),(3508269056,103758150570232,103758533068357)]
theorem point_links_checked26735 : (cuts26735.take 2).map (fun c => (3508142081-1+2*2^9*c.k,103757693882319+c.lower,103758076380183+c.upper)) = pointBounds26735 := by
 decide +kernel
def cuts26736 : List PrefixCut := [⟨104,394734279,394734495⟩,
⟨128,480659580,480659845⟩]
theorem checked26736 : checkPrefixCuts (2^48) 3508273153 9 Manual.Count131072.C026736.packed 128 cuts26736 = true := by
 decide +kernel
def pointBounds26736 : List (Nat × Nat × Nat) := [(3508379648,103758560869479,103758943367830)]
theorem point_links_checked26736 : (cuts26736.take 1).map (fun c => (3508273153-1+2*2^9*c.k,103758166135200+c.lower,103758548633335+c.upper)) = pointBounds26736 := by
 decide +kernel
def cuts26737 : List PrefixCut := [⟨84,309598981,309599153⟩,
⟨128,475105773,475106039⟩]
theorem checked26737 : checkPrefixCuts (2^48) 3508404225 9 Manual.Count131072.C026737.packed 128 cuts26737 = true := by
 decide +kernel
def pointBounds26737 : List (Nat × Nat × Nat) := [(3508490240,103758956393761,103759338892333)]
theorem point_links_checked26737 : (cuts26737.take 1).map (fun c => (3508404225-1+2*2^9*c.k,103758646794780+c.lower,103759029293180+c.upper)) = pointBounds26737 := by
 decide +kernel
def cuts26738 : List PrefixCut := [⟨64,237466023,237466154⟩,
⟨128,476130971,476131239⟩]
theorem checked26738 : checkPrefixCuts (2^48) 3508535297 9 Manual.Count131072.C026738.packed 128 cuts26738 = true := by
 decide +kernel
def pointBounds26738 : List (Nat × Nat × Nat) := [(3508600832,103759359366576,103759741865373)]
theorem point_links_checked26738 : (cuts26738.take 1).map (fun c => (3508535297-1+2*2^9*c.k,103759121900553+c.lower,103759504399219+c.upper)) = pointBounds26738 := by
 decide +kernel
def cuts26739 : List PrefixCut := [⟨44,164375379,164375473⟩,
⟨128,475712083,475712354⟩]
theorem checked26739 : checkPrefixCuts (2^48) 3508666369 9 Manual.Count131072.C026739.packed 128 cuts26739 = true := by
 decide +kernel
def pointBounds26739 : List (Nat × Nat × Nat) := [(3508711424,103759762406903,103760144905931)]
theorem point_links_checked26739 : (cuts26739.take 1).map (fun c => (3508666369-1+2*2^9*c.k,103759598031524+c.lower,103759980530458+c.upper)) = pointBounds26739 := by
 decide +kernel
def cuts26740 : List PrefixCut := [⟨24,90086477,90086526⟩,
⟨128,479223969,479224236⟩]
theorem checked26740 : checkPrefixCuts (2^48) 3508797441 9 Manual.Count131072.C026740.packed 128 cuts26740 = true := by
 decide +kernel
def pointBounds26740 : List (Nat × Nat × Nat) := [(3508822016,103760163830084,103760546329338)]
theorem point_links_checked26740 : (cuts26740.take 1).map (fun c => (3508797441-1+2*2^9*c.k,103760073743607+c.lower,103760456242812+c.upper)) = pointBounds26740 := by
 decide +kernel
def cuts26741 : List PrefixCut := [⟨4,15160961,15160969⟩,
⟨112,420088399,420088631⟩,
⟨128,482414643,482414910⟩]
theorem checked26741 : checkPrefixCuts (2^48) 3508928513 9 Manual.Count131072.C026741.packed 128 cuts26741 = true := by
 decide +kernel
def pointBounds26741 : List (Nat × Nat × Nat) := [(3508932608,103760568128537,103760950628017),(3509043200,103760973055975,103761355555679)]
theorem point_links_checked26741 : (cuts26741.take 2).map (fun c => (3508928513-1+2*2^9*c.k,103760552967576+c.lower,103760935467048+c.upper)) = pointBounds26741 := by
 decide +kernel
def cuts26742 : List PrefixCut := [⟨92,344032242,344032432⟩,
⟨128,480150634,480150901⟩]
theorem checked26742 : checkPrefixCuts (2^48) 3509059585 9 Manual.Count131072.C026742.packed 128 cuts26742 = true := by
 decide +kernel
def pointBounds26742 : List (Nat × Nat × Nat) := [(3509153792,103761379414461,103761761914390)]
theorem point_links_checked26742 : (cuts26742.take 1).map (fun c => (3509059585-1+2*2^9*c.k,103761035382219+c.lower,103761417881958+c.upper)) = pointBounds26742 := by
 decide +kernel
def cuts26743 : List PrefixCut := [⟨72,272874192,272874342⟩,
⟨128,477084886,477085147⟩]
theorem checked26743 : checkPrefixCuts (2^48) 3509190657 9 Manual.Count131072.C026743.packed 128 cuts26743 = true := by
 decide +kernel
def pointBounds26743 : List (Nat × Nat × Nat) := [(3509264384,103761788407045,103762170907201)]
theorem point_links_checked26743 : (cuts26743.take 1).map (fun c => (3509190657-1+2*2^9*c.k,103761515532853+c.lower,103761898032859+c.upper)) = pointBounds26743 := by
 decide +kernel
def cuts26744 : List PrefixCut := [⟨52,197951307,197951417⟩,
⟨128,482360603,482360871⟩]
theorem checked26744 : checkPrefixCuts (2^48) 3509321729 9 Manual.Count131072.C026744.packed 128 cuts26744 = true := by
 decide +kernel
def pointBounds26744 : List (Nat × Nat × Nat) := [(3509374976,103762190569046,103762573069423)]
theorem point_links_checked26744 : (cuts26744.take 1).map (fun c => (3509321729-1+2*2^9*c.k,103761992617739+c.lower,103762375118006+c.upper)) = pointBounds26744 := by
 decide +kernel
def cuts26745 : List PrefixCut := [⟨32,119584770,119584835⟩,
⟨128,473119244,473119507⟩]
theorem checked26745 : checkPrefixCuts (2^48) 3509452801 9 Manual.Count131072.C026745.packed 128 cuts26745 = true := by
 decide +kernel
def pointBounds26745 : List (Nat × Nat × Nat) := [(3509485568,103762594563112,103762977063712)]
theorem point_links_checked26745 : (cuts26745.take 1).map (fun c => (3509452801-1+2*2^9*c.k,103762474978342+c.lower,103762857478877+c.upper)) = pointBounds26745 := by
 decide +kernel
def cuts26746 : List PrefixCut := [⟨12,45634736,45634761⟩,
⟨120,450726092,450726342⟩,
⟨128,481281866,481282134⟩]
theorem checked26746 : checkPrefixCuts (2^48) 3509583873 9 Manual.Count131072.C026746.packed 128 cuts26746 = true := by
 decide +kernel
def pointBounds26746 : List (Nat × Nat × Nat) := [(3509596160,103762993732322,103763376233145),(3509706752,103763398823678,103763781324726)]
theorem point_links_checked26746 : (cuts26746.take 2).map (fun c => (3509583873-1+2*2^9*c.k,103762948097586+c.lower,103763330598384+c.upper)) = pointBounds26746 := by
 decide +kernel
def cuts26747 : List PrefixCut := [⟨100,371796135,371796343⟩,
⟨128,480782663,480782930⟩]
theorem checked26747 : checkPrefixCuts (2^48) 3509714945 9 Manual.Count131072.C026747.packed 128 cuts26747 = true := by
 decide +kernel
def pointBounds26747 : List (Nat × Nat × Nat) := [(3509817344,103763801175587,103764183676861)]
theorem point_links_checked26747 : (cuts26747.take 1).map (fun c => (3509714945-1+2*2^9*c.k,103763429379452+c.lower,103763811880518+c.upper)) = pointBounds26747 := by
 decide +kernel
def cuts26748 : List PrefixCut := [⟨80,300169368,300169530⟩,
⟨128,481326185,481326444⟩]
theorem checked26748 : checkPrefixCuts (2^48) 3509846017 9 Manual.Count131072.C026748.packed 128 cuts26748 = true := by
 decide +kernel
def pointBounds26748 : List (Nat × Nat × Nat) := [(3509927936,103764210331483,103764592832978)]
theorem point_links_checked26748 : (cuts26748.take 1).map (fun c => (3509846017-1+2*2^9*c.k,103763910162115+c.lower,103764292663448+c.upper)) = pointBounds26748 := by
 decide +kernel
def cuts26749 : List PrefixCut := [⟨60,226141725,226141848⟩,
⟨128,484435660,484435930⟩]
theorem checked26749 : checkPrefixCuts (2^48) 3509977089 9 Manual.Count131072.C026749.packed 128 cuts26749 = true := by
 decide +kernel
def pointBounds26749 : List (Nat × Nat × Nat) := [(3510038528,103764617630025,103765000131740)]
theorem point_links_checked26749 : (cuts26749.take 1).map (fun c => (3509977089-1+2*2^9*c.k,103764391488300+c.lower,103764773989892+c.upper)) = pointBounds26749 := by
 decide +kernel
def cuts26750 : List PrefixCut := [⟨40,151076707,151076794⟩,
⟨128,478483635,478483909⟩]
theorem checked26750 : checkPrefixCuts (2^48) 3510108161 9 Manual.Count131072.C026750.packed 128 cuts26750 = true := by
 decide +kernel
def pointBounds26750 : List (Nat × Nat × Nat) := [(3510149120,103765027000667,103765409502616)]
theorem point_links_checked26750 : (cuts26750.take 1).map (fun c => (3510108161-1+2*2^9*c.k,103764875923960+c.lower,103765258425822+c.upper)) = pointBounds26750 := by
 decide +kernel
def cuts26751 : List PrefixCut := [⟨20,75776317,75776357⟩,
⟨128,474777274,474777534⟩]
theorem checked26751 : checkPrefixCuts (2^48) 3510239233 9 Manual.Count131072.C026751.packed 128 cuts26751 = true := by
 decide +kernel
def pointBounds26751 : List (Nat × Nat × Nat) := [(3510259712,103765430183912,103765812686088),(3510370304,103765829184869,103766211687265)]
theorem point_links_checked26751 : (cuts26751.take 2).map (fun c => (3510239233-1+2*2^9*c.k,103765354407595+c.lower,103765736909731+c.upper)) = pointBounds26751 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000210
