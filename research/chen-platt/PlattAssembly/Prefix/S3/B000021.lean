import PlattAssemblyKernel
import PlattCertificates.Count131072.C020672
import PlattCertificates.Count131072.C020673
import PlattCertificates.Count131072.C020674
import PlattCertificates.Count131072.C020675
import PlattCertificates.Count131072.C020676
import PlattCertificates.Count131072.C020677
import PlattCertificates.Count131072.C020678
import PlattCertificates.Count131072.C020679
import PlattCertificates.Count131072.C020680
import PlattCertificates.Count131072.C020681
import PlattCertificates.Count131072.C020682
import PlattCertificates.Count131072.C020683
import PlattCertificates.Count131072.C020684
import PlattCertificates.Count131072.C020685
import PlattCertificates.Count131072.C020686
import PlattCertificates.Count131072.C020687
import PlattCertificates.Count131072.C020688
import PlattCertificates.Count131072.C020689
import PlattCertificates.Count131072.C020690
import PlattCertificates.Count131072.C020691
import PlattCertificates.Count131072.C020692
import PlattCertificates.Count131072.C020693
import PlattCertificates.Count131072.C020694
import PlattCertificates.Count131072.C020695
import PlattCertificates.Count131072.C020696
import PlattCertificates.Count131072.C020697
import PlattCertificates.Count131072.C020698
import PlattCertificates.Count131072.C020699
import PlattCertificates.Count131072.C020700
import PlattCertificates.Count131072.C020701
import PlattCertificates.Count131072.C020702
import PlattCertificates.Count131072.C020703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20672 : List PrefixCut := [⟨59,284536719,284536883⟩,
⟨128,621449967,621450323⟩]
theorem checked20672 : checkPrefixCuts (2^48) 2713452545 9 Manual.Count131072.C020672.packed 128 cuts20672 = true := by
 decide +kernel
def pointBounds20672 : List (Nat × Nat × Nat) := [(2713512960,100449082831053,100449463451231)]
theorem point_links_checked20672 : (cuts20672.take 1).map (fun c => (2713452545-1+2*2^9*c.k,100448798294334+c.lower,100449178914348+c.upper)) = pointBounds20672 := by
 decide +kernel
def cuts20673 : List PrefixCut := [⟨14,66385814,66385853⟩,
⟨97,470502098,470502372⟩,
⟨128,624116922,624117285⟩]
theorem checked20673 : checkPrefixCuts (2^48) 2713583617 9 Manual.Count131072.C020673.packed 128 cuts20673 = true := by
 decide +kernel
def pointBounds20673 : List (Nat × Nat × Nat) := [(2713597952,100449486130115,100449866750524),(2713682944,100449890246399,100450270867043)]
theorem point_links_checked20673 : (cuts20673.take 2).map (fun c => (2713583617-1+2*2^9*c.k,100449419744301+c.lower,100449800364671+c.upper)) = pointBounds20673 := by
 decide +kernel
def cuts20674 : List PrefixCut := [⟨52,256608387,256608537⟩,
⟨128,625953770,625954143⟩]
theorem checked20674 : checkPrefixCuts (2^48) 2713714689 9 Manual.Count131072.C020674.packed 128 cuts20674 = true := by
 decide +kernel
def pointBounds20674 : List (Nat × Nat × Nat) := [(2713767936,100450300469610,100450681090493)]
theorem point_links_checked20674 : (cuts20674.take 1).map (fun c => (2713714689-1+2*2^9*c.k,100450043861223+c.lower,100450424481956+c.upper)) = pointBounds20674 := by
 decide +kernel
def cuts20675 : List PrefixCut := [⟨7,33915770,33915790⟩,
⟨90,442350178,442350435⟩,
⟨128,626960794,626961163⟩]
theorem checked20675 : checkPrefixCuts (2^48) 2713845761 9 Manual.Count131072.C020675.packed 128 cuts20675 = true := by
 decide +kernel
def pointBounds20675 : List (Nat × Nat × Nat) := [(2713852928,100450703730763,100451084351889),(2713937920,100451112165171,100451492786534)]
theorem point_links_checked20675 : (cuts20675.take 2).map (fun c => (2713845761-1+2*2^9*c.k,100450669814993+c.lower,100451050436099+c.upper)) = pointBounds20675 := by
 decide +kernel
def cuts20676 : List PrefixCut := [⟨45,218521607,218521735⟩,
⟨128,620811495,620811853⟩]
theorem checked20676 : checkPrefixCuts (2^48) 2713976833 9 Manual.Count131072.C020676.packed 128 cuts20676 = true := by
 decide +kernel
def pointBounds20676 : List (Nat × Nat × Nat) := [(2714022912,100451515297394,100451895918997),(2714107904,100451917587282,100452298209115)]
theorem point_links_checked20676 : (cuts20676.take 2).map (fun c => (2713976833-1+2*2^9*c.k,100451296775787+c.lower,100451677397262+c.upper)) = pointBounds20676 := by
 decide +kernel
def cuts20677 : List PrefixCut := [⟨83,410988717,410988951⟩,
⟨128,632915165,632915527⟩]
theorem checked20677 : checkPrefixCuts (2^48) 2714107905 9 Manual.Count131072.C020677.packed 128 cuts20677 = true := by
 decide +kernel
def pointBounds20677 : List (Nat × Nat × Nat) := [(2714192896,100452328575999,100452709198066)]
theorem point_links_checked20677 : (cuts20677.take 1).map (fun c => (2714107905-1+2*2^9*c.k,100451917587282+c.lower,100452298209115+c.upper)) = pointBounds20677 := by
 decide +kernel
def cuts20678 : List PrefixCut := [⟨38,187493768,187493877⟩,
⟨121,593064237,593064576⟩,
⟨128,626662450,626662808⟩]
theorem checked20678 : checkPrefixCuts (2^48) 2714238977 9 Manual.Count131072.C020678.packed 128 cuts20678 = true := by
 decide +kernel
def pointBounds20678 : List (Nat × Nat × Nat) := [(2714277888,100452737996215,100453118618519),(2714362880,100453143566684,100453524189218)]
theorem point_links_checked20678 : (cuts20678.take 2).map (fun c => (2714238977-1+2*2^9*c.k,100452550502447+c.lower,100452931124642+c.upper)) = pointBounds20678 := by
 decide +kernel
def cuts20679 : List PrefixCut := [⟨76,376936994,376937207⟩,
⟨128,633476102,633476466⟩]
theorem checked20679 : checkPrefixCuts (2^48) 2714370049 9 Manual.Count131072.C020679.packed 128 cuts20679 = true := by
 decide +kernel
def pointBounds20679 : List (Nat × Nat × Nat) := [(2714447872,100453554101891,100453934724657)]
theorem point_links_checked20679 : (cuts20679.take 1).map (fun c => (2714370049-1+2*2^9*c.k,100453177164897+c.lower,100453557787450+c.upper)) = pointBounds20679 := by
 decide +kernel
def cuts20680 : List PrefixCut := [⟨31,149731885,149731971⟩,
⟨114,552153610,552153929⟩,
⟨128,620380526,620380884⟩]
theorem checked20680 : checkPrefixCuts (2^48) 2714501121 9 Manual.Count131072.C020680.packed 128 cuts20680 = true := by
 decide +kernel
def pointBounds20680 : List (Nat × Nat × Nat) := [(2714532864,100453960372884,100454340995887),(2714617856,100454362794609,100454743417845)]
theorem point_links_checked20680 : (cuts20680.take 2).map (fun c => (2714501121-1+2*2^9*c.k,100453810640999+c.lower,100454191263916+c.upper)) = pointBounds20680 := by
 decide +kernel
def cuts20681 : List PrefixCut := [⟨69,332937959,332938155⟩,
⟨128,615062623,615062983⟩]
theorem checked20681 : checkPrefixCuts (2^48) 2714632193 9 Manual.Count131072.C020681.packed 128 cuts20681 = true := by
 decide +kernel
def pointBounds20681 : List (Nat × Nat × Nat) := [(2714702848,100454763959484,100455144582955)]
theorem point_links_checked20681 : (cuts20681.take 1).map (fun c => (2714632193-1+2*2^9*c.k,100454431021525+c.lower,100454811644800+c.upper)) = pointBounds20681 := by
 decide +kernel
def cuts20682 : List PrefixCut := [⟨24,119338628,119338700⟩,
⟨107,528669138,528669447⟩,
⟨128,631207113,631207486⟩]
theorem checked20682 : checkPrefixCuts (2^48) 2714763265 9 Manual.Count131072.C020682.packed 128 cuts20682 = true := by
 decide +kernel
def pointBounds20682 : List (Nat × Nat × Nat) := [(2714787840,100455165422776,100455546046483),(2714872832,100455574753286,100455955377230)]
theorem point_links_checked20682 : (cuts20682.take 2).map (fun c => (2714763265-1+2*2^9*c.k,100455046084148+c.lower,100455426707783+c.upper)) = pointBounds20682 := by
 decide +kernel
def cuts20683 : List PrefixCut := [⟨62,296930387,296930560⟩,
⟨128,626718407,626718775⟩]
theorem checked20683 : checkPrefixCuts (2^48) 2714894337 9 Manual.Count131072.C020683.packed 128 cuts20683 = true := by
 decide +kernel
def pointBounds20683 : List (Nat × Nat × Nat) := [(2714957824,100455974221648,100456354845829)]
theorem point_links_checked20683 : (cuts20683.take 1).map (fun c => (2714894337-1+2*2^9*c.k,100455677291261+c.lower,100456057915269+c.upper)) = pointBounds20683 := by
 decide +kernel
def cuts20684 : List PrefixCut := [⟨17,82938146,82938194⟩,
⟨100,491089771,491090054⟩,
⟨128,627621249,627621612⟩]
theorem checked20684 : checkPrefixCuts (2^48) 2715025409 9 Manual.Count131072.C020684.packed 128 cuts20684 = true := by
 decide +kernel
def pointBounds20684 : List (Nat × Nat × Nat) := [(2715042816,100456386947814,100456767572238),(2715127808,100456795099439,100457175724098)]
theorem point_links_checked20684 : (cuts20684.take 2).map (fun c => (2715025409-1+2*2^9*c.k,100456304009668+c.lower,100456684634044+c.upper)) = pointBounds20684 := by
 decide +kernel
def cuts20685 : List PrefixCut := [⟨55,271400064,271400219⟩,
⟨128,622718843,622719204⟩]
theorem checked20685 : checkPrefixCuts (2^48) 2715156481 9 Manual.Count131072.C020685.packed 128 cuts20685 = true := by
 decide +kernel
def pointBounds20685 : List (Nat × Nat × Nat) := [(2715212800,100457203030981,100457583655875)]
theorem point_links_checked20685 : (cuts20685.take 1).map (fun c => (2715156481-1+2*2^9*c.k,100456931630917+c.lower,100457312255656+c.upper)) = pointBounds20685 := by
 decide +kernel
def cuts20686 : List PrefixCut := [⟨10,47166584,47166610⟩,
⟨93,450615240,450615505⟩,
⟨128,627042327,627042693⟩]
theorem checked20686 : checkPrefixCuts (2^48) 2715287553 9 Manual.Count131072.C020686.packed 128 cuts20686 = true := by
 decide +kernel
def pointBounds20686 : List (Nat × Nat × Nat) := [(2715297792,100457601516344,100457982141470),(2715382784,100458004965000,100458385590365)]
theorem point_links_checked20686 : (cuts20686.take 2).map (fun c => (2715287553-1+2*2^9*c.k,100457554349760+c.lower,100457934974860+c.upper)) = pointBounds20686 := by
 decide +kernel
def cuts20687 : List PrefixCut := [⟨48,232295469,232295603⟩,
⟨128,625664543,625664905⟩]
theorem checked20687 : checkPrefixCuts (2^48) 2715418625 9 Manual.Count131072.C020687.packed 128 cuts20687 = true := by
 decide +kernel
def pointBounds20687 : List (Nat × Nat × Nat) := [(2715467776,100458413687556,100458794313156)]
theorem point_links_checked20687 : (cuts20687.take 1).map (fun c => (2715418625-1+2*2^9*c.k,100458181392087+c.lower,100458562017553+c.upper)) = pointBounds20687 := by
 decide +kernel
def cuts20688 : List PrefixCut := [⟨3,15133330,15133338⟩,
⟨86,414501602,414501845⟩,
⟨128,615580321,615580681⟩]
theorem checked20688 : checkPrefixCuts (2^48) 2715549697 9 Manual.Count131072.C020688.packed 128 cuts20688 = true := by
 decide +kernel
def pointBounds20688 : List (Nat × Nat × Nat) := [(2715552768,100458822189960,100459202815796),(2715637760,100459221558232,100459602184303)]
theorem point_links_checked20688 : (cuts20688.take 2).map (fun c => (2715549697-1+2*2^9*c.k,100458807056630+c.lower,100459187682458+c.upper)) = pointBounds20688 := by
 decide +kernel
def cuts20689 : List PrefixCut := [⟨41,203666741,203666857⟩,
⟨124,614307359,614307712⟩,
⟨128,633584972,633585336⟩]
theorem checked20689 : checkPrefixCuts (2^48) 2715680769 9 Manual.Count131072.C020689.packed 128 cuts20689 = true := by
 decide +kernel
def pointBounds20689 : List (Nat × Nat × Nat) := [(2715722752,100459626303692,100460006929996),(2715807744,100460036944310,100460417570851)]
theorem point_links_checked20689 : (cuts20689.take 2).map (fun c => (2715680769-1+2*2^9*c.k,100459422636951+c.lower,100459803263139+c.upper)) = pointBounds20689 := by
 decide +kernel
def cuts20690 : List PrefixCut := [⟨79,382851532,382851758⟩,
⟨128,617593787,617594147⟩]
theorem checked20690 : checkPrefixCuts (2^48) 2715811841 9 Manual.Count131072.C020690.packed 128 cuts20690 = true := by
 decide +kernel
def pointBounds20690 : List (Nat × Nat × Nat) := [(2715892736,100460439073455,100460819700233)]
theorem point_links_checked20690 : (cuts20690.take 1).map (fun c => (2715811841-1+2*2^9*c.k,100460056221923+c.lower,100460436848475+c.upper)) = pointBounds20690 := by
 decide +kernel
def cuts20691 : List PrefixCut := [⟨34,164990646,164990742⟩,
⟨117,569478278,569478613⟩,
⟨128,623885716,623886081⟩]
theorem checked20691 : checkPrefixCuts (2^48) 2715942913 9 Manual.Count131072.C020691.packed 128 cuts20691 = true := by
 decide +kernel
def pointBounds20691 : List (Nat × Nat × Nat) := [(2715977728,100460838806356,100461219433364),(2716062720,100461243293988,100461623921235)]
theorem point_links_checked20691 : (cuts20691.take 2).map (fun c => (2715942913-1+2*2^9*c.k,100460673815710+c.lower,100461054442622+c.upper)) = pointBounds20691 := by
 decide +kernel
def cuts20692 : List PrefixCut := [⟨72,354938261,354938460⟩,
⟨128,628519084,628519442⟩]
theorem checked20692 : checkPrefixCuts (2^48) 2716073985 9 Manual.Count131072.C020692.packed 128 cuts20692 = true := by
 decide +kernel
def pointBounds20692 : List (Nat × Nat × Nat) := [(2716147712,100461652639687,100462033267163)]
theorem point_links_checked20692 : (cuts20692.take 1).map (fun c => (2716073985-1+2*2^9*c.k,100461297701426+c.lower,100461678328703+c.upper)) = pointBounds20692 := by
 decide +kernel
def cuts20693 : List PrefixCut := [⟨27,129948853,129948934⟩,
⟨110,538958002,538958318⟩,
⟨128,626726973,626727340⟩]
theorem checked20693 : checkPrefixCuts (2^48) 2716205057 9 Manual.Count131072.C020693.packed 128 cuts20693 = true := by
 decide +kernel
def pointBounds20693 : List (Nat × Nat × Nat) := [(2716232704,100462056169363,100462436797079),(2716317696,100462465178512,100462845806463)]
theorem point_links_checked20693 : (cuts20693.take 2).map (fun c => (2716205057-1+2*2^9*c.k,100461926220510+c.lower,100462306848145+c.upper)) = pointBounds20693 := by
 decide +kernel
def cuts20694 : List PrefixCut := [⟨65,316046278,316046460⟩,
⟨128,619132521,619132879⟩]
theorem checked20694 : checkPrefixCuts (2^48) 2716336129 9 Manual.Count131072.C020694.packed 128 cuts20694 = true := by
 decide +kernel
def pointBounds20694 : List (Nat × Nat × Nat) := [(2716402688,100462868993761,100463249621945)]
theorem point_links_checked20694 : (cuts20694.take 1).map (fun c => (2716336129-1+2*2^9*c.k,100462552947483+c.lower,100462933575485+c.upper)) = pointBounds20694 := by
 decide +kernel
def cuts20695 : List PrefixCut := [⟨20,97607793,97607846⟩,
⟨103,506578576,506578864⟩,
⟨128,630914761,630915119⟩]
theorem checked20695 : checkPrefixCuts (2^48) 2716467201 9 Manual.Count131072.C020695.packed 128 cuts20695 = true := by
 decide +kernel
def pointBounds20695 : List (Nat × Nat × Nat) := [(2716487680,100463269687797,100463650316210),(2716572672,100463678658580,100464059287228)]
theorem point_links_checked20695 : (cuts20695.take 2).map (fun c => (2716467201-1+2*2^9*c.k,100463172080004+c.lower,100463552708364+c.upper)) = pointBounds20695 := by
 decide +kernel
def cuts20696 : List PrefixCut := [⟨58,273431706,273431868⟩,
⟨128,614513758,614514120⟩]
theorem checked20696 : checkPrefixCuts (2^48) 2716598273 9 Manual.Count131072.C020696.packed 128 cuts20696 = true := by
 decide +kernel
def pointBounds20696 : List (Nat × Nat × Nat) := [(2716657664,100464076426471,100464457055351)]
theorem point_links_checked20696 : (cuts20696.take 1).map (fun c => (2716598273-1+2*2^9*c.k,100463802994765+c.lower,100464183623483+c.upper)) = pointBounds20696 := by
 decide +kernel
def cuts20697 : List PrefixCut := [⟨13,64858451,64858489⟩,
⟨96,472754789,472755062⟩,
⟨128,626813381,626813746⟩]
theorem checked20697 : checkPrefixCuts (2^48) 2716729345 9 Manual.Count131072.C020697.packed 128 cuts20697 = true := by
 decide +kernel
def pointBounds20697 : List (Nat × Nat × Nat) := [(2716742656,100464482366974,100464862996092),(2716827648,100464890263312,100465270892665)]
theorem point_links_checked20697 : (cuts20697.take 2).map (fun c => (2716729345-1+2*2^9*c.k,100464417508523+c.lower,100464798137603+c.upper)) = pointBounds20697 := by
 decide +kernel
def cuts20698 : List PrefixCut := [⟨51,247815964,247816107⟩,
⟨128,632688186,632688550⟩]
theorem checked20698 : checkPrefixCuts (2^48) 2716860417 9 Manual.Count131072.C020698.packed 128 cuts20698 = true := by
 decide +kernel
def pointBounds20698 : List (Nat × Nat × Nat) := [(2716912640,100465292137868,100465672767456)]
theorem point_links_checked20698 : (cuts20698.take 1).map (fun c => (2716860417-1+2*2^9*c.k,100465044321904+c.lower,100465424951349+c.upper)) = pointBounds20698 := by
 decide +kernel
def cuts20699 : List PrefixCut := [⟨6,29836191,29836207⟩,
⟨89,439973310,439973563⟩,
⟨128,627995984,627996344⟩]
theorem checked20699 : checkPrefixCuts (2^48) 2716991489 9 Manual.Count131072.C020699.packed 128 cuts20699 = true := by
 decide +kernel
def pointBounds20699 : List (Nat × Nat × Nat) := [(2716997632,100465706846281,100466087476106),(2717082624,100466116983400,100466497613462)]
theorem point_links_checked20699 : (cuts20699.take 2).map (fun c => (2716991489-1+2*2^9*c.k,100465677010090+c.lower,100466057639899+c.upper)) = pointBounds20699 := by
 decide +kernel
def cuts20700 : List PrefixCut := [⟨44,215368058,215368179⟩,
⟨127,619160535,619160892⟩,
⟨128,623511232,623511592⟩]
theorem checked20700 : checkPrefixCuts (2^48) 2717122561 9 Manual.Count131072.C020700.packed 128 cuts20700 = true := by
 decide +kernel
def pointBounds20700 : List (Nat × Nat × Nat) := [(2717167616,100466520374132,100466901004422),(2717252608,100466924166609,100467304797135)]
theorem point_links_checked20700 : (cuts20700.take 2).map (fun c => (2717122561-1+2*2^9*c.k,100466305006074+c.lower,100466685636243+c.upper)) = pointBounds20700 := by
 decide +kernel
def cuts20701 : List PrefixCut := [⟨82,408544694,408544928⟩,
⟨128,627003177,627003540⟩]
theorem checked20701 : checkPrefixCuts (2^48) 2717253633 9 Manual.Count131072.C020701.packed 128 cuts20701 = true := by
 decide +kernel
def pointBounds20701 : List (Nat × Nat × Nat) := [(2717337600,100467337062000,100467717692763)]
theorem point_links_checked20701 : (cuts20701.take 1).map (fun c => (2717253633-1+2*2^9*c.k,100466928517306+c.lower,100467309147835+c.upper)) = pointBounds20701 := by
 decide +kernel
def cuts20702 : List PrefixCut := [⟨37,180336763,180336868⟩,
⟨120,589373984,589374332⟩,
⟨128,626351392,626351761⟩]
theorem checked20702 : checkPrefixCuts (2^48) 2717384705 9 Manual.Count131072.C020702.packed 128 cuts20702 = true := by
 decide +kernel
def pointBounds20702 : List (Nat × Nat × Nat) := [(2717422592,100467735857246,100468116488243),(2717507584,100468144894467,100468525525707)]
theorem point_links_checked20702 : (cuts20702.take 2).map (fun c => (2717384705-1+2*2^9*c.k,100467555520483+c.lower,100467936151375+c.upper)) = pointBounds20702 := by
 decide +kernel
def cuts20703 : List PrefixCut := [⟨75,362828673,362828883⟩,
⟨128,623938872,623939231⟩]
theorem checked20703 : checkPrefixCuts (2^48) 2717515777 9 Manual.Count131072.C020703.packed 128 cuts20703 = true := by
 decide +kernel
def pointBounds20703 : List (Nat × Nat × Nat) := [(2717592576,100468544700548,100468925332019)]
theorem point_links_checked20703 : (cuts20703.take 1).map (fun c => (2717515777-1+2*2^9*c.k,100468181871875+c.lower,100468562503136+c.upper)) = pointBounds20703 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000021
