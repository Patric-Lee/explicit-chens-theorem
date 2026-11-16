import PlattAssemblyKernel
import PlattCertificates.Count131072.C017680
import PlattCertificates.Count131072.C017681
import PlattCertificates.Count131072.C017682
import PlattCertificates.Count131072.C017683
import PlattCertificates.Count131072.C017684
import PlattCertificates.Count131072.C017685
import PlattCertificates.Count131072.C017686
import PlattCertificates.Count131072.C017687
import PlattCertificates.Count131072.C017688
import PlattCertificates.Count131072.C017689
import PlattCertificates.Count131072.C017690
import PlattCertificates.Count131072.C017691
import PlattCertificates.Count131072.C017692
import PlattCertificates.Count131072.C017693
import PlattCertificates.Count131072.C017694
import PlattCertificates.Count131072.C017695
import PlattCertificates.Count131072.C017696
import PlattCertificates.Count131072.C017697
import PlattCertificates.Count131072.C017698
import PlattCertificates.Count131072.C017699
import PlattCertificates.Count131072.C017700
import PlattCertificates.Count131072.C017701
import PlattCertificates.Count131072.C017702
import PlattCertificates.Count131072.C017703
import PlattCertificates.Count131072.C017704
import PlattCertificates.Count131072.C017705
import PlattCertificates.Count131072.C017706
import PlattCertificates.Count131072.C017707
import PlattCertificates.Count131072.C017708
import PlattCertificates.Count131072.C017709
import PlattCertificates.Count131072.C017710
import PlattCertificates.Count131072.C017711
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000240
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17680 : List PrefixCut := [⟨44,252457146,252457302⟩,
⟨115,667994425,667994836⟩,
⟨128,741594211,741594668⟩]
theorem checked17680 : checkPrefixCuts (2^48) 2321285121 9 Manual.Count131072.C017680.packed 128 cuts17680 = true := by
 decide +kernel
def pointBounds17680 : List (Nat × Nat × Nat) := [(2321330176,98418942031591,98419321439207),(2321402880,98419357568870,98419736976741)]
theorem point_links_checked17680 : (cuts17680.take 2).map (fun c => (2321285121-1+2*2^9*c.k,98418689574445+c.lower,98419068981905+c.upper)) = pointBounds17680 := by
 decide +kernel
def cuts17681 : List PrefixCut := [⟨58,330527033,330527234⟩,
⟨128,732095042,732095498⟩]
theorem checked17681 : checkPrefixCuts (2^48) 2321416193 9 Manual.Count131072.C017681.packed 128 cuts17681 = true := by
 decide +kernel
def pointBounds17681 : List (Nat × Nat × Nat) := [(2321475584,98419761695689,98420141103807)]
theorem point_links_checked17681 : (cuts17681.take 1).map (fun c => (2321416193-1+2*2^9*c.k,98419431168656+c.lower,98419810576573+c.upper)) = pointBounds17681 := by
 decide +kernel
def cuts17682 : List PrefixCut := [⟨1,6183469,6183473⟩,
⟨72,414770883,414771140⟩,
⟨128,741631704,741632157⟩]
theorem checked17682 : checkPrefixCuts (2^48) 2321547265 9 Manual.Count131072.C017682.packed 128 cuts17682 = true := by
 decide +kernel
def pointBounds17682 : List (Nat × Nat × Nat) := [(2321548288,98420169447167,98420548855544),(2321620992,98420578034581,98420957443211)]
theorem point_links_checked17682 : (cuts17682.take 2).map (fun c => (2321547265-1+2*2^9*c.k,98420163263698+c.lower,98420542672071+c.upper)) = pointBounds17682 := by
 decide +kernel
def cuts17683 : List PrefixCut := [⟨15,84138672,84138724⟩,
⟨86,483365521,483365822⟩,
⟨128,726193121,726193571⟩]
theorem checked17683 : checkPrefixCuts (2^48) 2321678337 9 Manual.Count131072.C017683.packed 128 cuts17683 = true := by
 decide +kernel
def pointBounds17683 : List (Nat × Nat × Nat) := [(2321693696,98420989034074,98421368442952),(2321766400,98421388260923,98421767670050)]
theorem point_links_checked17683 : (cuts17683.take 2).map (fun c => (2321678337-1+2*2^9*c.k,98420904895402+c.lower,98421284304228+c.upper)) = pointBounds17683 := by
 decide +kernel
def cuts17684 : List PrefixCut := [⟨29,164994103,164994201⟩,
⟨100,570984634,570984983⟩,
⟨128,733062105,733062554⟩]
theorem checked17684 : checkPrefixCuts (2^48) 2321809409 9 Manual.Count131072.C017684.packed 128 cuts17684 = true := by
 decide +kernel
def pointBounds17684 : List (Nat × Nat × Nat) := [(2321839104,98421796082626,98422175492000),(2321911808,98422202073157,98422581482782)]
theorem point_links_checked17684 : (cuts17684.take 2).map (fun c => (2321809409-1+2*2^9*c.k,98421631088523+c.lower,98422010497799+c.upper)) = pointBounds17684 := by
 decide +kernel
def cuts17685 : List PrefixCut := [⟨43,251416161,251416317⟩,
⟨114,668291070,668291476⟩,
⟨128,748900724,748901181⟩]
theorem checked17685 : checkPrefixCuts (2^48) 2321940481 9 Manual.Count131072.C017685.packed 128 cuts17685 = true := by
 decide +kernel
def pointBounds17685 : List (Nat × Nat × Nat) := [(2321984512,98422615566789,98422994976670),(2322057216,98423032441698,98423411851829)]
theorem point_links_checked17685 : (cuts17685.take 2).map (fun c => (2321940481-1+2*2^9*c.k,98422364150628+c.lower,98422743560353+c.upper)) = pointBounds17685 := by
 decide +kernel
def cuts17686 : List PrefixCut := [⟨57,319766839,319767031⟩,
⟨128,729706482,729706927⟩]
theorem checked17686 : checkPrefixCuts (2^48) 2322071553 9 Manual.Count131072.C017686.packed 128 cuts17686 = true := by
 decide +kernel
def pointBounds17686 : List (Nat × Nat × Nat) := [(2322129920,98423432818191,98423812228565),(2322202624,98423842757834,98424222168461)]
theorem point_links_checked17686 : (cuts17686.take 2).map (fun c => (2322071553-1+2*2^9*c.k,98423113051352+c.lower,98423492461534+c.upper)) = pointBounds17686 := by
 decide +kernel
def cuts17687 : List PrefixCut := [⟨71,411866233,411866486⟩,
⟨128,739119735,739120186⟩]
theorem checked17687 : checkPrefixCuts (2^48) 2322202625 9 Manual.Count131072.C017687.packed 128 cuts17687 = true := by
 decide +kernel
def pointBounds17687 : List (Nat × Nat × Nat) := [(2322275328,98424254624067,98424634034947)]
theorem point_links_checked17687 : (cuts17687.take 1).map (fun c => (2322202625-1+2*2^9*c.k,98423842757834+c.lower,98424222168461+c.upper)) = pointBounds17687 := by
 decide +kernel
def cuts17688 : List PrefixCut := [⟨14,78175990,78176037⟩,
⟨85,486743969,486744266⟩,
⟨128,730593889,730594337⟩]
theorem checked17688 : checkPrefixCuts (2^48) 2322333697 9 Manual.Count131072.C017688.packed 128 cuts17688 = true := by
 decide +kernel
def pointBounds17688 : List (Nat × Nat × Nat) := [(2322348032,98424660053559,98425039464684),(2322420736,98425068621538,98425448032913)]
theorem point_links_checked17688 : (cuts17688.take 2).map (fun c => (2322333697-1+2*2^9*c.k,98424581877569+c.lower,98424961288647+c.upper)) = pointBounds17688 := by
 decide +kernel
def cuts17689 : List PrefixCut := [⟨28,164099209,164099311⟩,
⟨99,574338261,574338619⟩,
⟨128,739763359,739763821⟩]
theorem checked17689 : checkPrefixCuts (2^48) 2322464769 9 Manual.Count131072.C017689.packed 128 cuts17689 = true := by
 decide +kernel
def pointBounds17689 : List (Nat × Nat × Nat) := [(2322493440,98425476570667,98425855982295),(2322566144,98425886809719,98426266221603)]
theorem point_links_checked17689 : (cuts17689.take 2).map (fun c => (2322464769-1+2*2^9*c.k,98425312471458+c.lower,98425691882984+c.upper)) = pointBounds17689 := by
 decide +kernel
def cuts17690 : List PrefixCut := [⟨42,232561014,232561162⟩,
⟨113,643380272,643380679⟩,
⟨128,732450031,732450491⟩]
theorem checked17690 : checkPrefixCuts (2^48) 2322595841 9 Manual.Count131072.C017690.packed 128 cuts17690 = true := by
 decide +kernel
def pointBounds17690 : List (Nat × Nat × Nat) := [(2322638848,98426284795831,98426664207967),(2322711552,98426695615089,98427075027484)]
theorem point_links_checked17690 : (cuts17690.take 2).map (fun c => (2322595841-1+2*2^9*c.k,98426052234817+c.lower,98426431646805+c.upper)) = pointBounds17690 := by
 decide +kernel
def cuts17691 : List PrefixCut := [⟨56,320040240,320040432⟩,
⟨127,727198506,727198949⟩,
⟨128,732772608,732773055⟩]
theorem checked17691 : checkPrefixCuts (2^48) 2322726913 9 Manual.Count131072.C017691.packed 128 cuts17691 = true := by
 decide +kernel
def pointBounds17691 : List (Nat × Nat × Nat) := [(2322784256,98427104725088,98427484137728),(2322856960,98427511883354,98427891296245)]
theorem point_links_checked17691 : (cuts17691.take 2).map (fun c => (2322726913-1+2*2^9*c.k,98426784684848+c.lower,98427164097296+c.upper)) = pointBounds17691 := by
 decide +kernel
def cuts17692 : List PrefixCut := [⟨70,398299800,398300049⟩,
⟨128,732367698,732368154⟩]
theorem checked17692 : checkPrefixCuts (2^48) 2322857985 9 Manual.Count131072.C017692.packed 128 cuts17692 = true := by
 decide +kernel
def pointBounds17692 : List (Nat × Nat × Nat) := [(2322929664,98427915757256,98428295170400)]
theorem point_links_checked17692 : (cuts17692.take 1).map (fun c => (2322857985-1+2*2^9*c.k,98427517457456+c.lower,98427896870351+c.upper)) = pointBounds17692 := by
 decide +kernel
def cuts17693 : List PrefixCut := [⟨13,75367076,75367125⟩,
⟨84,484668039,484668341⟩,
⟨128,739959754,739960211⟩]
theorem checked17693 : checkPrefixCuts (2^48) 2322989057 9 Manual.Count131072.C017693.packed 128 cuts17693 = true := by
 decide +kernel
def pointBounds17693 : List (Nat × Nat × Nat) := [(2323002368,98428325192230,98428704605630),(2323075072,98428734493193,98429113906846)]
theorem point_links_checked17693 : (cuts17693.take 2).map (fun c => (2322989057-1+2*2^9*c.k,98428249825154+c.lower,98428629238505+c.upper)) = pointBounds17693 := by
 decide +kernel
def cuts17694 : List PrefixCut := [⟨27,156419757,156419854⟩,
⟨98,563150809,563151154⟩,
⟨128,737010247,737010702⟩]
theorem checked17694 : checkPrefixCuts (2^48) 2323120129 9 Manual.Count131072.C017694.packed 128 cuts17694 = true := by
 decide +kernel
def pointBounds17694 : List (Nat × Nat × Nat) := [(2323147776,98429146204665,98429525618570),(2323220480,98429552935717,98429932349870)]
theorem point_links_checked17694 : (cuts17694.take 2).map (fun c => (2323120129-1+2*2^9*c.k,98428989784908+c.lower,98429369198716+c.upper)) = pointBounds17694 := by
 decide +kernel
def cuts17695 : List PrefixCut := [⟨41,232616665,232616809⟩,
⟨112,655798944,655799343⟩,
⟨128,748962671,748963127⟩]
theorem checked17695 : checkPrefixCuts (2^48) 2323251201 9 Manual.Count131072.C017695.packed 128 cuts17695 = true := by
 decide +kernel
def pointBounds17695 : List (Nat × Nat × Nat) := [(2323293184,98429959411820,98430338826227),(2323365888,98430382594099,98430762008761)]
theorem point_links_checked17695 : (cuts17695.take 2).map (fun c => (2323251201-1+2*2^9*c.k,98429726795155+c.lower,98430106209418+c.upper)) = pointBounds17695 := by
 decide +kernel
def cuts17696 : List PrefixCut := [⟨55,311712038,311712225⟩,
⟨126,719724766,719725201⟩,
⟨128,730748686,730749128⟩]
theorem checked17696 : checkPrefixCuts (2^48) 2323382273 9 Manual.Count131072.C017696.packed 128 cuts17696 = true := by
 decide +kernel
def pointBounds17696 : List (Nat × Nat × Nat) := [(2323438592,98430787469864,98431166884770),(2323511296,98431195482592,98431574897746)]
theorem point_links_checked17696 : (cuts17696.take 2).map (fun c => (2323382273-1+2*2^9*c.k,98430475757826+c.lower,98430855172545+c.upper)) = pointBounds17696 := by
 decide +kernel
def cuts17697 : List PrefixCut := [⟨69,403517666,403517913⟩,
⟨128,735674447,735674896⟩]
theorem checked17697 : checkPrefixCuts (2^48) 2323513345 9 Manual.Count131072.C017697.packed 128 cuts17697 = true := by
 decide +kernel
def pointBounds17697 : List (Nat × Nat × Nat) := [(2323584000,98431610024178,98431989439586)]
theorem point_links_checked17697 : (cuts17697.take 1).map (fun c => (2323513345-1+2*2^9*c.k,98431206506512+c.lower,98431585921673+c.upper)) = pointBounds17697 := by
 decide +kernel
def cuts17698 : List PrefixCut := [⟨12,70137035,70137077⟩,
⟨83,473629547,473629833⟩,
⟨128,734179031,734179478⟩]
theorem checked17698 : checkPrefixCuts (2^48) 2323644417 9 Manual.Count131072.C017698.packed 128 cuts17698 = true := by
 decide +kernel
def pointBounds17698 : List (Nat × Nat × Nat) := [(2323656704,98432012317994,98432391733646),(2323729408,98432415810506,98432795226402)]
theorem point_links_checked17698 : (cuts17698.take 2).map (fun c => (2323644417-1+2*2^9*c.k,98431942180959+c.lower,98432321596569+c.upper)) = pointBounds17698 := by
 decide +kernel
def cuts17699 : List PrefixCut := [⟨26,149592551,149592640⟩,
⟨97,565899198,565899538⟩,
⟨128,742495441,742495890⟩]
theorem checked17699 : checkPrefixCuts (2^48) 2323775489 9 Manual.Count131072.C017699.packed 128 cuts17699 = true := by
 decide +kernel
def pointBounds17699 : List (Nat × Nat × Nat) := [(2323802112,98432825952541,98433205368687),(2323874816,98433242259188,98433621675585)]
theorem point_links_checked17699 : (cuts17699.take 2).map (fun c => (2323775489-1+2*2^9*c.k,98432676359990+c.lower,98433055776047+c.upper)) = pointBounds17699 := by
 decide +kernel
def cuts17700 : List PrefixCut := [⟨40,228796374,228796515⟩,
⟨111,633207398,633207781⟩,
⟨128,731795047,731795492⟩]
theorem checked17700 : checkPrefixCuts (2^48) 2323906561 9 Manual.Count131072.C017700.packed 128 cuts17700 = true := by
 decide +kernel
def pointBounds17700 : List (Nat × Nat × Nat) := [(2323947520,98433647651805,98434027068452),(2324020224,98434052062829,98434431479718)]
theorem point_links_checked17700 : (cuts17700.take 2).map (fun c => (2323906561-1+2*2^9*c.k,98433418855431+c.lower,98433798271937+c.upper)) = pointBounds17700 := by
 decide +kernel
def cuts17701 : List PrefixCut := [⟨54,313077489,313077681⟩,
⟨125,718674284,718674723⟩,
⟨128,735266059,735266508⟩]
theorem checked17701 : checkPrefixCuts (2^48) 2324037633 9 Manual.Count131072.C017701.packed 128 cuts17701 = true := by
 decide +kernel
def pointBounds17701 : List (Nat × Nat × Nat) := [(2324092928,98434463727967,98434843145110),(2324165632,98434869324762,98435248742152)]
theorem point_links_checked17701 : (cuts17701.take 2).map (fun c => (2324037633-1+2*2^9*c.k,98434150650478+c.lower,98434530067429+c.upper)) = pointBounds17701 := by
 decide +kernel
def cuts17702 : List PrefixCut := [⟨68,392746614,392746857⟩,
⟨128,738978726,738979181⟩]
theorem checked17702 : checkPrefixCuts (2^48) 2324168705 9 Manual.Count131072.C017702.packed 128 cuts17702 = true := by
 decide +kernel
def pointBounds17702 : List (Nat × Nat × Nat) := [(2324238336,98435278663151,98435658080794)]
theorem point_links_checked17702 : (cuts17702.take 1).map (fun c => (2324168705-1+2*2^9*c.k,98434885916537+c.lower,98435265333937+c.upper)) = pointBounds17702 := by
 decide +kernel
def cuts17703 : List PrefixCut := [⟨11,59581518,59581558⟩,
⟨82,472406056,472406349⟩,
⟨128,738815790,738816248⟩]
theorem checked17703 : checkPrefixCuts (2^48) 2324299777 9 Manual.Count131072.C017703.packed 128 cuts17703 = true := by
 decide +kernel
def pointBounds17703 : List (Nat × Nat × Nat) := [(2324311040,98435684476781,98436063894676),(2324383744,98436097301319,98436476719467)]
theorem point_links_checked17703 : (cuts17703.take 2).map (fun c => (2324299777-1+2*2^9*c.k,98435624895263+c.lower,98436004313118+c.upper)) = pointBounds17703 := by
 decide +kernel
def cuts17704 : List PrefixCut := [⟨25,142648072,142648159⟩,
⟨96,544669890,544670226⟩,
⟨128,728118418,728118868⟩]
theorem checked17704 : checkPrefixCuts (2^48) 2324430849 9 Manual.Count131072.C017704.packed 128 cuts17704 = true := by
 decide +kernel
def pointBounds17704 : List (Nat × Nat × Nat) := [(2324456448,98436506359125,98436885777525),(2324529152,98436908380943,98437287799592)]
theorem point_links_checked17704 : (cuts17704.take 2).map (fun c => (2324430849-1+2*2^9*c.k,98436363711053+c.lower,98436743129366+c.upper)) = pointBounds17704 := by
 decide +kernel
def cuts17705 : List PrefixCut := [⟨39,226310210,226310345⟩,
⟨110,641746995,641747388⟩,
⟨128,742970650,742971104⟩]
theorem checked17705 : checkPrefixCuts (2^48) 2324561921 9 Manual.Count131072.C017705.packed 128 cuts17705 = true := by
 decide +kernel
def pointBounds17705 : List (Nat × Nat × Nat) := [(2324601856,98437318139681,98437697558579),(2324674560,98437733576466,98438112995622)]
theorem point_links_checked17705 : (cuts17705.take 2).map (fun c => (2324561921-1+2*2^9*c.k,98437091829471+c.lower,98437471248234+c.upper)) = pointBounds17705 := by
 decide +kernel
def cuts17706 : List PrefixCut := [⟨53,301607927,301608117⟩,
⟨124,717018881,717019324⟩,
⟨128,740265039,740265495⟩]
theorem checked17706 : checkPrefixCuts (2^48) 2324692993 9 Manual.Count131072.C017706.packed 128 cuts17706 = true := by
 decide +kernel
def pointBounds17706 : List (Nat × Nat × Nat) := [(2324747264,98438136408048,98438515827455),(2324819968,98438551819002,98438931238662)]
theorem point_links_checked17706 : (cuts17706.take 2).map (fun c => (2324692993-1+2*2^9*c.k,98437834800121+c.lower,98438214219338+c.upper)) = pointBounds17706 := by
 decide +kernel
def cuts17707 : List PrefixCut := [⟨67,381497317,381497548⟩,
⟨128,732353629,732354077⟩]
theorem checked17707 : checkPrefixCuts (2^48) 2324824065 9 Manual.Count131072.C017707.packed 128 cuts17707 = true := by
 decide +kernel
def pointBounds17707 : List (Nat × Nat × Nat) := [(2324892672,98438956562477,98439335982381)]
theorem point_links_checked17707 : (cuts17707.take 1).map (fun c => (2324824065-1+2*2^9*c.k,98438575065160+c.lower,98438954484833+c.upper)) = pointBounds17707 := by
 decide +kernel
def cuts17708 : List PrefixCut := [⟨10,55206344,55206377⟩,
⟨81,464888230,464888512⟩,
⟨128,740907899,740908350⟩]
theorem checked17708 : checkPrefixCuts (2^48) 2324955137 9 Manual.Count131072.C017708.packed 128 cuts17708 = true := by
 decide +kernel
def pointBounds17708 : List (Nat × Nat × Nat) := [(2324965376,98439362625133,98439742045287),(2325038080,98439772307019,98440151727422)]
theorem point_links_checked17708 : (cuts17708.take 2).map (fun c => (2324955137-1+2*2^9*c.k,98439307418789+c.lower,98439686838910+c.upper)) = pointBounds17708 := by
 decide +kernel
def cuts17709 : List PrefixCut := [⟨24,137160236,137160319⟩,
⟨95,541247838,541248163⟩,
⟨128,724886792,724887233⟩]
theorem checked17709 : checkPrefixCuts (2^48) 2325086209 9 Manual.Count131072.C017709.packed 128 cuts17709 = true := by
 decide +kernel
def pointBounds17709 : List (Nat × Nat × Nat) := [(2325110784,98440185486924,98440564907579),(2325183488,98440589574526,98440968995423)]
theorem point_links_checked17709 : (cuts17709.take 2).map (fun c => (2325086209-1+2*2^9*c.k,98440048326688+c.lower,98440427747260+c.upper)) = pointBounds17709 := by
 decide +kernel
def cuts17710 : List PrefixCut := [⟨38,220072792,220072929⟩,
⟨109,617598498,617598878⟩,
⟨128,726419610,726420057⟩]
theorem checked17710 : checkPrefixCuts (2^48) 2325217281 9 Manual.Count131072.C017710.packed 128 cuts17710 = true := by
 decide +kernel
def pointBounds17710 : List (Nat × Nat × Nat) := [(2325256192,98440993286272,98441372707422),(2325328896,98441390811978,98441770233371)]
theorem point_links_checked17710 : (cuts17710.take 2).map (fun c => (2325217281-1+2*2^9*c.k,98440773213480+c.lower,98441152634493+c.upper)) = pointBounds17710 := by
 decide +kernel
def cuts17711 : List PrefixCut := [⟨52,302491316,302491501⟩,
⟨123,714275012,714275449⟩,
⟨128,744171804,744172258⟩]
theorem checked17711 : checkPrefixCuts (2^48) 2325348353 9 Manual.Count131072.C017711.packed 128 cuts17711 = true := by
 decide +kernel
def pointBounds17711 : List (Nat × Nat × Nat) := [(2325401600,98441802124406,98442181546051),(2325474304,98442213908102,98442593329999)]
theorem point_links_checked17711 : (cuts17711.take 2).map (fun c => (2325348353-1+2*2^9*c.k,98441499633090+c.lower,98441879054550+c.upper)) = pointBounds17711 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000240
